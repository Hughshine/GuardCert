(* Untrusted bound and predicate proposals on actual generated code. The
   range-restricted final checker and accepted capture remain authoritative. *)
include GuardSelectedDoublePointCoordinates

let minimum a b = if Z.compare a b <= 0 then a else b
let maximum a b = if Z.compare a b >= 0 then a else b
let interval_sum (a,b) (c,d) = Z.add a c, Z.add b d
let interval_scale factor (a,b) =
  if Z.sign factor >= 0 then Z.mul factor a,Z.mul factor b
  else Z.mul factor b,Z.mul factor a
let rec interval bounds = function
  | L.Constant value -> let value = GuardMemoryNumbers.export_integer value in Some (value,value)
  | L.Var index -> List.nth_opt bounds (GuardOpenScopDoubleIO.nat_to_int index) |> Option.join
  | L.Sum (a,b) -> (match interval bounds a,interval bounds b with
      | Some a,Some b -> Some (interval_sum a b) | _ -> None)
  | L.Mult (factor,value) -> Option.map (interval_scale (GuardMemoryNumbers.export_integer factor)) (interval bounds value)
  | L.Div (value,divisor) ->
      let divisor = GuardMemoryNumbers.export_integer divisor in
      if Z.sign divisor <= 0 then None else Option.map (fun (a,b) -> Z.ediv a divisor,Z.ediv b divisor) (interval bounds value)
  | L.Max (a,b) -> (match interval bounds a,interval bounds b with
      | Some (a,b),Some (c,d) -> Some (maximum a c,maximum b d) | _ -> None)
  | L.Min (a,b) -> (match interval bounds a,interval bounds b with
      | Some (a,b),Some (c,d) -> Some (minimum a c,minimum b d) | _ -> None)
  | L.Mod _ -> None

(* A paired affine lower/upper leaf preserves a real tile's local width.
   Choosing any leaves is only a proposal; the whole candidate is rechecked. *)
let paired_bounds lower upper =
  List.fold_left (fun best lo -> List.fold_left (fun best hi ->
    match linear (subtract hi lo),best with
    | Some (coefficients,width),_ when Coefficients.is_empty coefficients && Z.sign width > 0 ->
        (match best with Some (_,_,old) when Z.compare old width <= 0 -> best
         | _ -> Some (lo,hi,width))
    | _ -> best) best (min_leaves upper)) None (max_leaves lower)

let bounded_adaptation limit code =
  let proposals = ref [] in
  let mode = Sys.getenv_opt "GUARDCERT_BOUND_NORMALIZATION" in
  let rec adapt depth bounds = function
    | L.Loop (lower,upper,body) ->
        let lo,hi,reason = match paired_bounds lower upper with
          | Some (lo,hi,width) -> lo,hi,"local-affine-width=" ^ Z.to_string width
          | None ->
              let lo = match interval bounds lower with
                | Some (value,_) -> L.Constant (integer value)
                | None -> choose depth (L.Constant (small 0)) (max_leaves lower) in
              let hi = match interval bounds upper with
                | Some (_,value) -> L.Constant (integer value)
                | None -> choose depth (upper_enclosure upper) (min_leaves upper) in
              lo,hi,"captured-range-interval-proposal" in
        let hi = if depth = 0 && mode = Some "wrong-bound" then L.Constant (small 0) else hi in
        proposals := (Printf.sprintf "depth=%d %s lower=%s upper=%s" depth reason
          (loop_expression lo) (loop_expression hi)) :: !proposals;
        let next = match interval bounds lo,interval bounds hi with
          | Some (lo,_),Some (_,hi) -> Some (lo,maximum lo hi)
          | _ -> None in
        let body = adapt (depth+1) (next::bounds) body in
        let body = if mode = Some "retain-membership" then
          L.Guard (L.And (lower_membership (shift lower) (L.Var (nat 0)),
            upper_membership (L.Var (nat 0)) (shift upper)),body) else body in
        L.Loop (lo,hi,body)
    | L.Guard (test,body) -> L.Guard (test,adapt depth bounds body)
    | L.Instr (_,args) as body ->
        if mode = Some "wrong-point-domain" then body else
        let parameter = L.Var (nat depth) in
        let tests = List.map (fun coordinate -> L.And (L.LE (L.Constant (small 0),coordinate),
          L.LE (add coordinate one,parameter))) args in
        let test = List.fold_right (fun test rest -> L.And (test,rest)) tests (L.TConstantTest true) in
        L.Guard (test,body)
    | L.Seq sequence -> L.Seq (adapt_sequence depth bounds sequence)
  and adapt_sequence depth bounds = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (adapt depth bounds head,adapt_sequence depth bounds tail) in
  let result = adapt 0 [Some (Z.zero,GuardMemoryNumbers.export_integer limit)] code in
  result,String.concat "\n" (List.rev !proposals) ^ "\n"

let adapt limit (((raw,context),variables) as request) =
  if Sys.getenv_opt "GUARDCERT_BOUND_NORMALIZATION" = Some "disabled" || List.length context <> 1 then
    GuardSelectedDoublePointCoordinates.adapt limit request
  else (
    incr adaptations;
    try
      let path = match !current_path with Some path -> path | None -> failwith "missing tiling phase receipt" in
      emit (Filename.concat path "raw-generated.loop") (statement "" raw);
      let enabled = Sys.getenv_opt "GUARDCERT_POINT_NORMALIZATION" <> Some "disabled" in
      let without_singletons,singletons = if enabled then singleton_eliminate raw else raw,0 in
      let recovered,translations = if enabled then recover_points without_singletons else without_singletons,0 in
      emit (Filename.concat path "point-normalized.loop") (statement "" recovered);
      emit (Filename.concat path "point-normalization.txt")
        (Printf.sprintf "enabled=%b singleton_loops_removed=%d point_translations=%d\n" enabled singletons translations);
      let unit_links = List.exists (fun witness -> List.exists (fun link ->
        Z.equal (GuardMemoryNumbers.export_integer link.TilingWitness.tl_tile_size) Z.one)
        witness.TilingWitness.stw_links) !current_witnesses in
      let completed = if unit_links then (
        if not (List.for_all canonical !current_witnesses) then
          invalid_arg "affine unit coordinates require a new completion proposal";
        Coordinates.complete_unit_points (Coordinates.unit_axes !current_witnesses) recovered) else recovered in
      emit (Filename.concat path "completed.loop") (statement "" completed);
      emit (Filename.concat path "coordinate-completion.txt") ("unit-links=" ^ string_of_bool unit_links ^ "\n");
      emit (Filename.concat path "adaptation-limit.txt") (integer_text limit ^ "\n");
      let generated,proposals = bounded_adaptation limit completed in
      let generated = if Sys.getenv_opt "GUARDCERT_POINT_NORMALIZATION" = Some "wrong-coordinate" then
        let rec damage = function
          | L.Instr (instruction,first::rest) -> L.Instr (instruction,add first one::rest)
          | L.Loop (a,b,body) -> L.Loop (a,b,damage body)
          | L.Guard (test,body) -> L.Guard (test,damage body)
          | L.Seq sequence -> L.Seq (damage_sequence sequence)
          | code -> code
        and damage_sequence = function
          | L.SNil -> L.SNil
          | L.SCons (head,tail) -> L.SCons (damage head,damage_sequence tail) in
        damage generated else generated in
      emit (Filename.concat path "bounded-proposals.txt") proposals;
      emit (Filename.concat path "generated.loop") (statement "" generated);
      emit (Filename.concat path "adaptation.txt")
        "raw-phase-checks=accepted\nprepared-codegen=successful\nbounded-parameter-check=required\npoint-and-bound-adaptation=proposed\nfinal-candidate-check=pending\n";
      Result.Okk ((generated,context),variables)
    with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
      (match !current_path with Some path -> emit (Filename.concat path "adaptation-refusal.txt")
        (Printexc.to_string error ^ "\n") | None -> ());
      Result.Err (Printexc.to_string error))
