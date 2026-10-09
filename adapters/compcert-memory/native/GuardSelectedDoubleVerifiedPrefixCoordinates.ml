(* Verified predicate construction is a service; bounds, hoisting and unit
   completion remain untrusted proposals checked by the unchanged final checker. *)
include GuardSelectedDoublePrunedUnitCoordinates
module Membership = GuardMemoryDoubleFloorMembership.DoubleFloorMembership
let verified_predicates = ref 0
let cleared_floor_nodes = ref 0
let rec floor_nodes = function
  | L.Div (value,_) -> 1 + floor_nodes value
  | L.Sum (a,b) | L.Max (a,b) | L.Min (a,b) -> floor_nodes a + floor_nodes b
  | L.Mult (_,a) | L.Mod (a,_) -> floor_nodes a
  | _ -> 0
let membership bound = function
  | Some test -> incr verified_predicates;
      cleared_floor_nodes := !cleared_floor_nodes + floor_nodes bound; test
  | None -> invalid_arg "verified floor-membership service refused unsupported bound"
let lower_membership bound point = membership bound (Membership.lower_membership bound point)
let upper_membership point bound = membership bound (Membership.upper_membership point bound)

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
    verified_predicates := 0; cleared_floor_nodes := 0;
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
        complete_permuted_unit_points (Coordinates.unit_axes !current_witnesses) recovered) else recovered in
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
      emit (Filename.concat path "verified-membership.txt")
        (Printf.sprintf "verified-predicates=%d cleared-floor-nodes=%d\n" !verified_predicates !cleared_floor_nodes);
      emit (Filename.concat path "bounded-proposals.txt") proposals;
      emit (Filename.concat path "generated.loop") (statement "" generated);
      emit (Filename.concat path "adaptation.txt")
        "raw-phase-checks=accepted\nprepared-codegen=successful\nbounded-parameter-check=required\npoint-and-bound-adaptation=proposed\nfinal-candidate-check=pending\n";
      Result.Okk ((generated,context),variables)
    with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
      (match !current_path with Some path -> emit (Filename.concat path "adaptation-refusal.txt")
        (Printexc.to_string error ^ "\n") | None -> ());
      Result.Err (Printexc.to_string error))
