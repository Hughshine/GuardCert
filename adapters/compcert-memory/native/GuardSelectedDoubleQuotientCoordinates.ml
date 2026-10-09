(* Verified predicate construction is a service; bounds, hoisting and unit
   completion remain untrusted proposals checked by the unchanged final checker. *)
include GuardSelectedDoubleVerifiedPrefixCoordinates
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

let bounded_adaptation limit divisor code =
  let divisor = GuardMemoryNumbers.export_integer divisor in
  if Z.sign divisor <= 0 then invalid_arg "positive quotient divisor required";
  let cap = GuardMemoryNumbers.export_integer limit in
  let quotient_cap = Z.ediv (Z.add cap (Z.pred divisor)) divisor in
  if Z.sign quotient_cap <= 0 then invalid_arg "positive quotient cap required";
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
        let prefix = match point_arity body with Some dimensions -> depth < dimensions | None -> false in
        let hi,reason = if prefix then match interval bounds hi with
          | Some (_,upper) ->
              let factor = Z.ediv (Z.add (maximum Z.zero upper) (Z.pred quotient_cap)) quotient_cap in
              L.Mult (integer factor,L.Var (nat depth)),
              "quotient-affine-prefix-factor=" ^ Z.to_string factor
          | None -> hi,reason
          else hi,reason in
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
        let parameter = L.Var (nat (depth+1)) in
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
  let result = adapt 0 [Some (Z.zero,quotient_cap);Some (Z.zero,cap)] code in
  let result,moved = if Sys.getenv_opt "GUARDCERT_TILE_PRUNING" = Some "disabled" then result,0
    else hoist_independent result in
  result,String.concat "\n" (List.rev !proposals) ^
    Printf.sprintf "\nprefix-pruning=%b hoisted-factors=%d\n"
      (Sys.getenv_opt "GUARDCERT_TILE_PRUNING" <> Some "disabled") moved

let quotient_adapt limit divisor ((raw,context),variables) =
  if Sys.getenv_opt "GUARDCERT_BOUND_NORMALIZATION" = Some "disabled" || List.length context <> 2 then
    Result.Err "quotient adaptation disabled or extended context absent"
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
      let generated,proposals = bounded_adaptation limit divisor completed in
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
      emit (Filename.concat path "quotient-proposals.txt") proposals;
      emit (Filename.concat path "quotient-parameter.txt")
        ("divisor=" ^ integer_text divisor ^ "\nlayout=quotient,original-bound\nrelation=0<=d*q-n<=d-1\n");
      emit (Filename.concat path "generated.loop") (statement "" generated);
      emit (Filename.concat path "adaptation.txt")
        "raw-phase-checks=accepted\nprepared-codegen=successful\nquotient-relation-check=required\npoint-and-bound-adaptation=proposed\nfinal-candidate-check=pending\n";
      Result.Okk ((generated,context),variables)
    with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
      (match !current_path with Some path -> emit (Filename.concat path "adaptation-refusal.txt")
        (Printexc.to_string error ^ "\n") | None -> ());
      Result.Err (Printexc.to_string error))

(* Invalid policy data refuse the new pass; the established compiler still
   processes the actual intermediate program. No unmarked source depends on
   the mathematical sufficiency of this proposal. *)
let divisor () =
  let values = try
    String.split_on_char ',' (Option.value (Sys.getenv_opt "GUARDCERT_TILE_SIZES") ~default:"32")
    |> List.map Z.of_string
    with Invalid_argument _ | Failure _ -> [] in
  let value = match values with
    | [] -> Z.zero
    | first::rest when List.for_all (fun d -> Z.sign d > 0 && Z.compare d (Z.of_int 1024) <= 0) values ->
        List.fold_left minimum first rest
    | _ -> Z.zero in
  integer value

let private_count () =
  let original = GuardSelectedDoubleVerifiedPrefixCoordinates.private_count () in
  if Option.is_some (Sys.getenv_opt "GUARDCERT_DOUBLE_PRIVATE_COUNT") then original
  else Datatypes.S (Datatypes.S original)

let configure program =
  GuardSelectedDoubleVerifiedPrefixCoordinates.configure program;
  Printf.eprintf
    "GUARDCERT_DOUBLE_POLICY source_loop_depth=%d private_count=%d witness_axes=%d private_override=%b witness_override=%b\n%!"
    !source_depth (GuardOpenScopDoubleIO.nat_to_int (private_count ()))
    (match Sys.getenv_opt "GUARDCERT_DOUBLE_WITNESS_AXES" with None -> !proposed_witness_axes | Some text -> int_of_string text)
    (Option.is_some (Sys.getenv_opt "GUARDCERT_DOUBLE_PRIVATE_COUNT"))
    (Option.is_some (Sys.getenv_opt "GUARDCERT_DOUBLE_WITNESS_AXES"));
  Printf.eprintf "GUARDCERT_QUOTIENT_POLICY divisor=%s private_count=%d\n%!"
    (integer_text (divisor ())) (GuardOpenScopDoubleIO.nat_to_int (private_count ()))

let fallback_adapt = GuardSelectedDoubleVerifiedPrefixCoordinates.adapt

let quotient_guard program = function
  | Clight.Ssequence (capture,Clight.Sifthenelse (Clight.Etempvar (flag,_),
      Clight.Ssequence ((Clight.Sset (quotient,_) as quotient_capture),
        Clight.Ssequence (_,restore)),source)) ->
    (match GuardMemoryDoubleReductionNestData.checked_double_reduction_raw_nest program [] source with
     | Some description ->
       (match List.find_opt (fun id -> id <> flag) (GuardSelectedDoubleCandidate.assigned_temps capture) with
        | Some cache ->
          let limit = ReductionDoubleRegionFactory.reduction_double_limit description in
          capture = GuardMemoryLongRangeCapture.memory_long_range_capture
            description.GuardMemoryDoubleReductionNestData.reduction_nest_header cache flag limit &&
          restore = GuardMemoryDoubleReductionNestExitCode.double_reduction_exit_code
            description.GuardMemoryDoubleReductionNestData.reduction_nest_iterators cache &&
          (match GuardMemoryDoubleQuotientLowering.compile_double_ceil_capture cache quotient limit (divisor ()) with
           | Some (expected,_) -> expected = quotient_capture | None -> false)
        | None -> false)
     | None -> false)
  | _ -> false

let rec quotient_count program source =
  if quotient_guard program source then 1 else match source with
  | Clight.Ssequence (first,second) | Clight.Sloop (first,second) ->
      quotient_count program first + quotient_count program second
  | Clight.Sifthenelse (_,yes,no) -> quotient_count program yes + quotient_count program no
  | Clight.Slabel (_,body) -> quotient_count program body
  | Clight.Sswitch (_,cases) -> quotient_cases program cases
  | _ -> 0
and quotient_cases program = function
  | Clight.LSnil -> 0
  | Clight.LScons (_,body,rest) -> quotient_count program body + quotient_cases program rest

let trace_clight program =
  GuardSelectedDoubleVerifiedPrefixCoordinates.trace_clight program;
  let original,initialized,old_reduction,quotient = List.fold_left
    (fun (original,initialized,old_reduction,quotient) (_,definition) -> match definition with
     | AST.Gfun (Ctypes.Internal fn) ->
         original + GuardOriginalMatmulRawCandidate.guarded_statement fn.Clight.fn_body,
         initialized + GuardSelectedDoubleCandidate.initialized_count program fn.Clight.fn_body,
         old_reduction + GuardSelectedReductionCandidate.reduction_count program fn.Clight.fn_body,
         quotient + quotient_count program fn.Clight.fn_body
     | _ -> original,initialized,old_reduction,quotient) (0,0,0,0) program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_DOUBLE_INSTALLED original=%d initialized=%d regions=%d pipeline_calls=%d reduction=%d\n%!"
    original initialized (original+initialized+old_reduction+quotient)
    !GuardSelectedDoubleCandidate.calls (old_reduction+quotient);
  Printf.eprintf "GUARDCERT_DOUBLE_TILING_INSTALLED reduction=%d phase_calls=%d adaptations=%d enabled=%b\n%!"
    (old_reduction+quotient) !calls !adaptations (enabled ());
  Printf.eprintf "GUARDCERT_QUOTIENT_TILING_INSTALLED regions=%d older_reduction_regions=%d divisor=%s\n%!"
    quotient old_reduction (integer_text (divisor ()))
