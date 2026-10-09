(* Independent parameters, caps and normalized bounds are data proposals.
   The extracted factory checks source shape, footprints and the actual candidate. *)
include GuardSelectedDoubleVerifiedPrefixCoordinates
module Source = GuardMemoryDoubleRectangularNestDecoder
module Bounds = GuardMemoryDoubleRectangularNestEntry
module Capture = GuardMemoryDoubleRectangularNestCapture
module Exit = GuardMemoryDoubleRectangularExitCode

let caps_proposal description =
  let rank = List.length description.Source.rectangular_nest_axes in
  let fits caps = Bounds.double_rectangular_entry_bounds_check caps description in
  let search propose =
    let rec loop fuel low high =
      if fuel = 0 || Z.equal low high then low else
      let middle = Z.div (Z.add (Z.add low high) Z.one) (Z.of_int 2) in
      if fits (propose (integer middle)) then loop (fuel-1) middle high
      else loop (fuel-1) low (Z.pred middle) in
    integer (loop 32 Z.zero (Z.of_string "2147483647")) in
  let caps = match Sys.getenv_opt "GUARDCERT_RECTANGULAR_CAPS" with
    | Some text -> List.map (fun item -> integer (Z.of_string item)) (String.split_on_char ',' text)
    | None ->
      let shared = search (fun value -> List.init rank (fun _ -> value)) in
      let caps = List.init rank (fun _ -> shared) in
      List.fold_left (fun caps axis ->
        let replace value = List.mapi (fun index old -> if index=axis then value else old) caps in
        replace (search replace)) caps (List.init rank Fun.id) in
  Printf.eprintf "GUARDCERT_RECTANGULAR_CAPS rank=%d values=%s checked=%b\n%!"
    rank (String.concat "," (List.map integer_text caps)) (fits caps);
  caps

let rectangular_bounds caps code =
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
          lo,hi,"independent-captured-ranges" in
      let hi = if depth=0 && mode=Some "wrong-bound" then L.Constant (small 0) else hi in
      proposals := (Printf.sprintf "depth=%d %s lower=%s upper=%s" depth reason
        (loop_expression lo) (loop_expression hi)) :: !proposals;
      let next = match interval bounds lo,interval bounds hi with
        | Some (lo,_),Some (_,hi) -> Some (lo,maximum lo hi) | _ -> None in
      let body = adapt (depth+1) (next::bounds) body in
      let prefix = match point_arity body with Some dimensions -> depth < dimensions | None -> false in
      let body = if mode=Some "retain-membership" ||
        (Sys.getenv_opt "GUARDCERT_TILE_PRUNING" <> Some "disabled" && prefix) then
        L.Guard (L.And (lower_membership (shift lower) (L.Var (nat 0)),
          upper_membership (L.Var (nat 0)) (shift upper)),body) else body in
      L.Loop (lo,hi,body)
    | L.Guard (test,body) -> L.Guard (test,adapt depth bounds body)
    | L.Instr (_,args) as body ->
      if List.length args <> List.length caps then
        invalid_arg "rectangular instruction coordinate rank differs from parameters";
      if mode=Some "wrong-point-domain" then body else
      let tests = List.mapi (fun axis coordinate ->
        L.And (L.LE (L.Constant (small 0),coordinate),
          L.LE (add coordinate one,L.Var (nat (depth+axis))))) args in
      (match tests with [] -> body | first::rest ->
        L.Guard (List.fold_left (fun left right -> L.And (left,right)) first rest,body))
    | L.Seq sequence -> L.Seq (adapt_sequence depth bounds sequence)
  and adapt_sequence depth bounds = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (adapt depth bounds head,adapt_sequence depth bounds tail) in
  let bounds = List.map (fun cap -> Some (Z.zero,GuardMemoryNumbers.export_integer cap)) caps in
  let result = adapt 0 bounds code in
  let result,moved = if Sys.getenv_opt "GUARDCERT_TILE_PRUNING"=Some "disabled" then result,0
    else hoist_independent result in
  result,String.concat "\n" (List.rev !proposals) ^ Printf.sprintf "\nhoisted-factors=%d\n" moved

let adapt caps ((raw,context),variables) =
  incr adaptations;
  verified_predicates := 0; cleared_floor_nodes := 0;
  try
    if List.length context <> List.length caps then
      invalid_arg "rectangular candidate parameter layout differs from captures";
    let path = match !current_path with Some path -> path | None -> failwith "missing phase receipt" in
    emit (Filename.concat path "rectangular-raw-generated.loop") (statement "" raw);
    let without_singletons,singletons = singleton_eliminate raw in
    let recovered,translations = recover_points without_singletons in
    emit (Filename.concat path "rectangular-point-normalized.loop") (statement "" recovered);
    let unit_links = List.exists (fun witness -> List.exists (fun link ->
      Z.equal (GuardMemoryNumbers.export_integer link.TilingWitness.tl_tile_size) Z.one)
      witness.TilingWitness.stw_links) !current_witnesses in
    let completed = if unit_links then (
      if not (List.for_all canonical !current_witnesses) then
        invalid_arg "noncanonical rectangular unit coordinates need another proposal";
      complete_permuted_unit_points (Coordinates.unit_axes !current_witnesses) recovered) else recovered in
    let generated,proposals = rectangular_bounds caps completed in
    let generated = if Sys.getenv_opt "GUARDCERT_POINT_NORMALIZATION"=Some "wrong-coordinate" then
      let rec damage = function
        | L.Instr (instruction,first::rest) -> L.Instr (instruction,add first one::rest)
        | L.Loop (a,b,body) -> L.Loop (a,b,damage body)
        | L.Guard (test,body) -> L.Guard (test,damage body)
        | L.Seq sequence -> L.Seq (damage_sequence sequence) | code -> code
      and damage_sequence = function
        | L.SNil -> L.SNil
        | L.SCons (head,tail) -> L.SCons (damage head,damage_sequence tail) in
      damage generated else generated in
    emit (Filename.concat path "rectangular-caps.txt") (String.concat "," (List.map integer_text caps)^"\n");
    emit (Filename.concat path "rectangular-bounded-proposals.txt") proposals;
    emit (Filename.concat path "rectangular-generated.loop") (statement "" generated);
    emit (Filename.concat path "rectangular-normalization.txt")
      (Printf.sprintf "singleton-loops=%d point-translations=%d unit-links=%b predicates=%d floor-nodes=%d\nfinal-check=pending\n"
        singletons translations unit_links !verified_predicates !cleared_floor_nodes);
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
    (match !current_path with Some path -> emit (Filename.concat path "rectangular-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None -> ());
    Result.Err (Printexc.to_string error)

let rectangular_source program = function
  | Clight.Ssequence (capture,Clight.Sifthenelse (Clight.Etempvar (flag,_),
      Clight.Ssequence (_,restore),fallback)) ->
    (match Source.checked_double_rectangular_raw_nest program [] fallback with
      | None -> None
      | Some description ->
        let caches = GuardSelectedDoubleCandidate.assigned_temps capture |>
          List.filter (fun id -> id<>flag) |>
          List.fold_left (fun ids id -> if List.mem id ids then ids else ids@[id]) [] in
        let caps = caps_proposal description in
        (match Capture.double_rectangular_capture_steps description.Source.rectangular_nest_axes caches caps with
          | Some steps when capture=GuardMemoryRectangularCapture.rectangular_capture_code steps flag &&
              restore=Exit.double_rectangular_exit_code
                (List.map fst description.Source.rectangular_nest_axes) caches -> Some (fallback,description)
          | _ -> None))
  | _ -> None

let rec kinds program source = match rectangular_source program source with
  | Some _ -> 1,0,0,0
  | None ->
    (match GuardSelectedDoubleHeaderQuotient.header_quotient_source program source,
      GuardSelectedDoubleQuotientPartitioned.quotient_source program source with
      | Some _,_ -> 0,1,0,0
      | _,Some _ -> 0,0,1,0
      | _ -> if GuardSelectedReductionCandidate.reduction_guard program source then 0,0,0,1
        else match source with
        | Clight.Ssequence (a,b) | Clight.Sloop (a,b) | Clight.Sifthenelse (_,a,b) ->
          let ra,ha,qa,oa=kinds program a in let rb,hb,qb,ob=kinds program b in
          ra+rb,ha+hb,qa+qb,oa+ob
        | Clight.Slabel (_,body) -> kinds program body
        | Clight.Sswitch (_,cases) -> case_kinds program cases
        | _ -> 0,0,0,0)
and case_kinds program = function
  | Clight.LSnil -> 0,0,0,0
  | Clight.LScons (_,body,rest) ->
    let ra,ha,qa,oa=kinds program body in let rb,hb,qb,ob=case_kinds program rest in
    ra+rb,ha+hb,qa+qb,oa+ob

let trace_clight program =
  GuardSelectedDoubleHeaderQuotientV2.trace_clight program;
  let rectangular,header,quotient,older,initialized,original = List.fold_left
    (fun (r,h,q,o,i,m) (_,definition) -> match definition with
      | AST.Gfun (Ctypes.Internal fn) ->
        let rr,hh,qq,oo=kinds program fn.Clight.fn_body in
        r+rr,h+hh,q+qq,o+oo,
        i+GuardSelectedDoubleCandidate.initialized_count program fn.Clight.fn_body,
        m+GuardOriginalMatmulRawCandidate.guarded_statement fn.Clight.fn_body
      | _ -> r,h,q,o,i,m) (0,0,0,0,0,0) program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_RECTANGULAR_INSTALLED regions=%d\n%!" rectangular;
  Printf.eprintf "GUARDCERT_DOUBLE_INSTALLED original=%d initialized=%d regions=%d pipeline_calls=%d reduction=%d\n%!"
    original initialized (rectangular+header+quotient+older+initialized+original)
    !GuardSelectedDoubleCandidate.calls (rectangular+header+quotient+older);
  Printf.eprintf "GUARDCERT_DOUBLE_TILING_INSTALLED reduction=%d phase_calls=%d adaptations=%d enabled=%b\n%!"
    (rectangular+header+quotient+older) !calls !adaptations (enabled ())
