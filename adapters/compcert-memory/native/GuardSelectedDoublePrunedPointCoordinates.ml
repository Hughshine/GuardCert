(* Untrusted bound and predicate proposals on actual generated code. The
   range-restricted final checker and accepted capture remain authoritative. *)
include GuardSelectedDoubleBoundedPointCoordinatesV2

(* Pure prefix predicates and hoisting are proposals. Their actual emitted
   domains, schedules and instruction arguments are checked independently. *)
let rec point_arity = function
  | L.Instr (_,args) -> Some (List.length args)
  | L.Loop (_,_,body) | L.Guard (_,body) -> point_arity body
  | L.Seq sequence -> sequence_arity sequence
and sequence_arity = function
  | L.SNil -> None
  | L.SCons (head,tail) -> (match point_arity head,sequence_arity tail with
      | None,value | value,None -> value
      | Some a,Some b -> Some (min a b))
let rec factors = function
  | L.And (a,b) -> factors a @ factors b
  | test -> [test]
let guard tests body = match tests with
  | [] -> body
  | first::rest -> L.Guard (List.fold_left (fun a b -> L.And (a,b)) first rest,body)
let rec remove_inner_expression = function
  | L.Constant _ as expression -> expression
  | L.Var index ->
      let index = GuardOpenScopDoubleIO.nat_to_int index in
      if index = 0 then invalid_arg "test uses inner iterator" else L.Var (nat (index-1))
  | L.Sum (a,b) -> L.Sum (remove_inner_expression a,remove_inner_expression b)
  | L.Mult (k,a) -> L.Mult (k,remove_inner_expression a)
  | L.Div (a,k) -> L.Div (remove_inner_expression a,k)
  | L.Mod (a,k) -> L.Mod (remove_inner_expression a,k)
  | L.Max (a,b) -> L.Max (remove_inner_expression a,remove_inner_expression b)
  | L.Min (a,b) -> L.Min (remove_inner_expression a,remove_inner_expression b)
let rec remove_inner_test = function
  | L.LE (a,b) -> L.LE (remove_inner_expression a,remove_inner_expression b)
  | L.EQ (a,b) -> L.EQ (remove_inner_expression a,remove_inner_expression b)
  | L.And (a,b) -> L.And (remove_inner_test a,remove_inner_test b)
  | L.Or (a,b) -> L.Or (remove_inner_test a,remove_inner_test b)
  | L.Not a -> L.Not (remove_inner_test a)
  | L.TConstantTest _ as test -> test
let hoist_independent code =
  let moved = ref 0 in
  let rec normalize = function
    | L.Loop (lo,hi,body) ->
        let body = normalize body in
        (match body with
         | L.Guard (test,rest) ->
             let outside,inside = List.fold_right (fun test (outside,inside) ->
               try let lifted = remove_inner_test test in
                 incr moved; lifted::outside,inside
               with Invalid_argument _ -> outside,test::inside) (factors test) ([],[]) in
             guard outside (L.Loop (lo,hi,guard inside rest))
         | body -> L.Loop (lo,hi,body))
    | L.Guard (test,body) -> L.Guard (test,normalize body)
    | L.Seq sequence -> L.Seq (normalize_sequence sequence)
    | code -> code
  and normalize_sequence = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (normalize head,normalize_sequence tail) in
  let result = normalize code in result,!moved

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
        let prefix = match point_arity body with Some dimensions -> depth < dimensions | None -> false in
        let prune = Sys.getenv_opt "GUARDCERT_TILE_PRUNING" <> Some "disabled" in
        let body = if mode = Some "retain-membership" || (prune && prefix) then
          L.Guard (L.And (lower_membership (shift lower) (L.Var (nat 0)),
            upper_membership (L.Var (nat 0)) (shift upper)),body) else body in
        L.Loop (lo,hi,body)
    | L.Guard (test,body) -> L.Guard (test,adapt depth bounds body)
    | L.Instr (_,args) as body ->
        if mode = Some "wrong-point-domain" then body else
        let parameter = L.Var (nat depth) in
        let tests = List.map (fun coordinate -> L.And (L.LE (L.Constant (small 0),coordinate),
          L.LE (add coordinate one,parameter))) args in
        (* The affine extractor accepts LE, EQ and And, but rejects a
           TConstantTest leaf. Build the same box without that sentinel. *)
        (match tests with
         | [] -> body
         | first::rest ->
             let test = List.fold_left (fun left right -> L.And (left,right)) first rest in
             L.Guard (test,body))
    | L.Seq sequence -> L.Seq (adapt_sequence depth bounds sequence)
  and adapt_sequence depth bounds = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (adapt depth bounds head,adapt_sequence depth bounds tail) in
  let result = adapt 0 [Some (Z.zero,GuardMemoryNumbers.export_integer limit)] code in
  let result,moved = if Sys.getenv_opt "GUARDCERT_TILE_PRUNING" = Some "disabled" then result,0
    else hoist_independent result in
  result,String.concat "\n" (List.rev !proposals) ^
    Printf.sprintf "\nprefix-pruning=%b hoisted-factors=%d\n"
      (Sys.getenv_opt "GUARDCERT_TILE_PRUNING" <> Some "disabled") moved

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
