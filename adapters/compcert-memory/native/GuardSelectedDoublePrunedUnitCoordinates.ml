(* Untrusted completion preserves actual non-unit argument coordinates.
   Unit slots still refer to their checked canonical tile-axis proposals. *)
include GuardSelectedDoublePrunedPointCoordinates

let validate_permuted_point_slots units code =
  let dimensions = List.length units in
  let nonunit = List.filter (fun axis -> not (List.nth units axis)) (List.init dimensions Fun.id) in
  let expected_depth = dimensions + List.length nonunit in
  let rec check depth = function
    | L.Loop (_,_,body) -> check (depth+1) body
    | L.Guard (_,body) -> check depth body
    | L.Instr (_,args) ->
        let coordinates = List.filteri (fun index _ -> index < dimensions) args in
        let actual = List.map (function L.Var index -> GuardOpenScopDoubleIO.nat_to_int index
          | _ -> invalid_arg "non-variable source coordinate in unit proposal") coordinates in
        if depth <> expected_depth || List.length actual <> dimensions then
          invalid_arg "generated depth outside unit completion";
        List.iter (fun axis -> if List.nth units axis &&
          List.nth actual axis <> expected_depth-1-axis then
          invalid_arg "unit point does not match its tile-axis proposal") (List.init dimensions Fun.id);
        let nonunit_actual = List.map (List.nth actual) nonunit |> List.sort compare in
        if nonunit_actual <> List.init (List.length nonunit) Fun.id then
          invalid_arg "non-unit point slots are not a permutation"
    | L.Seq sequence -> check_sequence depth sequence
  and check_sequence depth = function
    | L.SNil -> ()
    | L.SCons (head,tail) -> check depth head; check_sequence depth tail in
  check 0 code

let complete_permuted_unit_points units code =
  let dimensions = List.length units in
  validate_permuted_point_slots units code;
  let rec complete depth axis code =
    if depth >= dimensions && axis < dimensions && List.nth units axis then
      let lo = L.Var (nat (depth-1-axis)) in
      L.Loop (lo,add lo one,complete (depth+1) (axis+1) (Coordinates.lift_statement 0 code))
    else match code with
    | L.Loop (lo,hi,body) when depth < dimensions -> L.Loop (lo,hi,complete (depth+1) axis body)
    | L.Loop (lo,hi,body) when axis < dimensions -> L.Loop (lo,hi,complete (depth+1) (axis+1) body)
    | L.Guard (test,body) -> L.Guard (test,complete depth axis body)
    | L.Instr (instruction,args) when depth = 2*dimensions && axis = dimensions ->
        L.Instr (instruction,List.mapi (fun index coordinate ->
          if index < dimensions && List.nth units index then L.Var (nat (dimensions-1-index))
          else coordinate) args)
    | L.Seq sequence -> L.Seq (complete_sequence depth axis sequence)
    | _ -> invalid_arg "generated loop skeleton outside unit completion"
  and complete_sequence depth axis = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (complete depth axis head,complete_sequence depth axis tail) in
  complete 0 0 code

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
      emit (Filename.concat path "bounded-proposals.txt") proposals;
      emit (Filename.concat path "generated.loop") (statement "" generated);
      emit (Filename.concat path "adaptation.txt")
        "raw-phase-checks=accepted\nprepared-codegen=successful\nbounded-parameter-check=required\npoint-and-bound-adaptation=proposed\nfinal-candidate-check=pending\n";
      Result.Okk ((generated,context),variables)
    with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
      (match !current_path with Some path -> emit (Filename.concat path "adaptation-refusal.txt")
        (Printexc.to_string error ^ "\n") | None -> ());
      Result.Err (Printexc.to_string error))
