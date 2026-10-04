(* Both policies are untrusted. The extracted source, domain, dependence and
   backend checks decide whether their result can enter a guarded region. *)
module L = GuardMemoryLoops.L
let nat = GuardMemoryCandidate.natural
let rec natural_size = function Datatypes.O -> 0 | Datatypes.S rest -> 1 + natural_size rest
let integer value = GuardMemoryNumbers.import_integer (Z.of_int value)
let mode () = match Sys.getenv_opt "GUARDCERT_AFFINE_MODE" with Some value -> value | None -> "interchange"
let diagnostic text = if Sys.getenv_opt "GUARDCERT_AFFINE_DIAGNOSTICS" = Some "1" then prerr_endline text
let last_source = ref None

let configured_integer variable fallback =
  let value = match Sys.getenv_opt variable with Some value -> value | None -> fallback in
  if String.length value > 128 then invalid_arg "affine range policy integer";
  GuardMemoryNumbers.import_integer (Z.of_string value)
let range_policy () = {
  AffineNestRangeProposal.affine_policy_root_floor = configured_integer "GUARDCERT_AFFINE_FLOOR" "-4";
  AffineNestRangeProposal.affine_policy_root_cap = configured_integer "GUARDCERT_AFFINE_CAP" "8";
  AffineNestRangeProposal.affine_policy_bound_lower = configured_integer "GUARDCERT_AFFINE_BOUND_LOW" "-8";
  AffineNestRangeProposal.affine_policy_bound_upper = configured_integer "GUARDCERT_AFFINE_BOUND_HIGH" "9";
  AffineNestRangeProposal.affine_policy_address_lower = configured_integer "GUARDCERT_AFFINE_ADDRESS_LOW" "-32";
  AffineNestRangeProposal.affine_policy_address_upper = configured_integer "GUARDCERT_AFFINE_ADDRESS_HIGH" "33";
}

let describe live pool source =
  let result = try
    AffineNestMultiProposal.affine_reserve_multi_scans
      (fun live pool source ->
    if Sys.getenv_opt "GUARDCERT_AFFINE_PROFILE" = Some "inferred"
    then AffineNestRangeProposal.affine_source_range_proposal (range_policy ()) live pool source
    else AffineNestPropose.affine_default_source_proposal live pool source) live pool source
    with Invalid_argument _ | Failure _ | Stack_overflow -> None in
  (match result with
   | None -> ()
   | Some (parameters, proposal) ->
       last_source := Some (live,pool,parameters,proposal);
       let axes = 1 + List.length proposal.AffineNestGuardPackage.affine_proposed_remaining in
       diagnostic (Printf.sprintf "GUARDCERT_AFFINE_SOURCE depth=%d pointers=%d" axes
         (List.length proposal.AffineNestGuardPackage.affine_proposed_pointers)));
  result

let rec split_source headers = function
  | L.Loop (lower,upper,body) -> split_source ((lower,upper)::headers) body
  | leaf -> List.rev headers, leaf

(* Undo the candidate's loop-coordinate permutation for domain alignment.
   These are suggestions to the proved point-space checker, not certificates
   trusted by the driver. *)
let permutation_steps permutation =
  let current = Array.of_list permutation in
  let steps = ref [] in
  for destination = 0 to Array.length current - 1 do
    let position = ref destination in
    while !position < Array.length current && current.(!position) <> destination do
      incr position
    done;
    if !position = Array.length current then invalid_arg "affine permutation";
    while !position > destination do
      let first = !position - 1 in
      let saved = current.(first) in
      current.(first) <- current.(!position); current.(!position) <- saved;
      steps := GuardMemoryAffineReindex.MemoryReindexSwap (nat first) :: !steps;
      decr position
    done
  done;
  List.rev !steps

let box_candidate request permutation keep_domain =
  let headers, leaf = split_source [] request.AffineNestCheckedCompiler.affine_requested_loop in
  let dimensions = List.length headers in
  let axes = request.AffineNestCheckedCompiler.affine_requested_axes in
  if List.length axes <> dimensions || List.length permutation <> dimensions then invalid_arg "affine box shape";
  let position source_axis =
    let rec search index = function
      | [] -> invalid_arg "affine permutation"
      | first::rest -> if first=source_axis then index else search (index+1) rest in
    search 0 permutation in
  let coordinate axis = L.Var (nat (dimensions-1-position axis)) in
  let rec expression depth = function
    | L.Var variable ->
        let index = natural_size variable in
        if index < depth then coordinate (depth-1-index)
        else L.Var (nat (dimensions+index-depth))
    | L.Sum (first,second) -> L.Sum (expression depth first,expression depth second)
    | L.Mult (factor,value) -> L.Mult (factor,expression depth value)
    | L.Div (value,divisor) -> L.Div (expression depth value,divisor)
    | L.Mod (value,divisor) -> L.Mod (expression depth value,divisor)
    | L.Min (first,second) -> L.Min (expression depth first,expression depth second)
    | L.Max (first,second) -> L.Max (expression depth first,expression depth second)
    | constant -> constant in
  let rec statement = function
    | L.Instr (instruction,arguments) -> L.Instr (instruction,List.map (expression dimensions) arguments)
    | L.Seq statements -> L.Seq (sequence statements)
    | _ -> invalid_arg "affine leaf is not a checked instruction sequence"
  and sequence = function
    | L.SNil -> L.SNil
    | L.SCons (first,rest) -> L.SCons (statement first,sequence rest) in
  let constraints = List.mapi (fun axis (lower,upper) ->
    L.And (L.LE (expression axis lower,coordinate axis),
      L.LE (coordinate axis,L.Sum (expression axis upper,L.Constant (integer (-1)))))) headers in
  let domain = match constraints with
    | [] -> invalid_arg "empty affine domain"
    | first::rest -> List.fold_left (fun previous test -> L.And (previous,test)) first rest in
  let leaf = statement leaf in
  let body = if keep_domain then L.Guard (domain,leaf) else leaf in
  List.fold_right (fun axis body ->
    let floor,cap = List.nth axes axis in L.Loop (L.Constant floor,L.Constant cap,body)) permutation body

let mapped_candidate candidate steps =
  Some (candidate,AffineNestCandidateEvidence.AffineIndexEvidence steps)
let tiled_candidate request boxed rows columns =
  let candidate,witnesses = GuardAffineNestTiling.propose request boxed rows columns in
  Some (candidate,AffineNestCandidateEvidence.AffineTilingEvidence witnesses)

let propose_raw request =
  try
    let selected = mode () in
    let dimensions = List.length request.AffineNestCheckedCompiler.affine_requested_axes in
    diagnostic (Printf.sprintf "GUARDCERT_AFFINE_REQUEST depth=%d mode=%s" dimensions selected);
    let order = List.init dimensions (fun index -> index) in
    let source = request.AffineNestCheckedCompiler.affine_requested_loop in
    match selected with
    | "disabled" -> None
    | "identity" -> mapped_candidate source []
    | "box" -> mapped_candidate (box_candidate request order true) []
    | "interchange" when dimensions>=2 ->
        let permutation = 1::0::List.init (dimensions-2) (fun index->index+2) in
        let steps = if Sys.getenv_opt "GUARDCERT_AFFINE_REINDEX" = Some "none"
          then [] else permutation_steps permutation in
        mapped_candidate (box_candidate request permutation true) steps
    | "reverse" ->
        let permutation = List.rev order in
        mapped_candidate (box_candidate request permutation true) (permutation_steps permutation)
    | "tile-2-3" -> tiled_candidate request (box_candidate request order true) 2 3
    | "tile-17-13" -> tiled_candidate request (box_candidate request order true) 17 13
    | "tile-1-1" -> tiled_candidate request (box_candidate request order true) 1 1
    | "wrong-tiling-witness" ->
        let boxed = box_candidate request order true in
        let candidate,_ = GuardAffineNestTiling.propose request boxed 2 3 in
        let _,wrong = GuardAffineNestTiling.propose request boxed 5 7 in
        Some (candidate,AffineNestCandidateEvidence.AffineTilingEvidence wrong)
    | "missing-tiling-witness" ->
        let candidate,_ = GuardAffineNestTiling.propose request (box_candidate request order true) 2 3 in
        Some (candidate,AffineNestCandidateEvidence.AffineTilingEvidence [])
    | "invalid-tile-size" -> tiled_candidate request (box_candidate request order true) 0 3
    | "oversized-tile-policy" -> tiled_candidate request (box_candidate request order true) 2048 2048
    | "invalid-domain" -> mapped_candidate (box_candidate request order false) []
    | "noop-reindex" -> mapped_candidate source [GuardMemoryAffineReindex.MemoryReindexSwap (nat 99)]
    | "wrong-reindex" -> mapped_candidate source [GuardMemoryAffineReindex.MemoryReindexSwap (nat 0)]
    | _ -> None
  with Invalid_argument _ | Failure _ | Stack_overflow -> None

let propose request =
  let result = propose_raw request in
  (match result,!last_source with
   | Some (candidate,evidence),Some (live,pool,parameters,proposal)
       when Sys.getenv_opt "GUARDCERT_AFFINE_DIAGNOSTICS" = Some "1" ->
       let compiled = match GuardMemoryTiledCompiler.private_counter_pairs pool with
         | None -> false
         | Some pairs -> GuardMemoryWindowBackend.compile_window_multi_pointer_buffer_loop
             proposal.AffineNestGuardPackage.affine_proposed_pointers
             (AffineNestPackageDecode.affine_package_context parameters proposal)
             (AffineNestPackageRanges.affine_package_encoder_bounds proposal) live pairs candidate <> None in
       diagnostic (Printf.sprintf "GUARDCERT_AFFINE_BACKEND compiled=%b" compiled);
       let context = AffineNestPackageDecode.affine_package_context parameters proposal in
       let bounds = AffineNestPackageRanges.affine_package_validator_bounds proposal in
       let variables = List.map (fun identifier -> identifier,())
         (context @ proposal.AffineNestGuardPackage.affine_proposed_pointers) in
       let extract loop = GuardMemoryExtractorTrace.MemoryExtractor.extractor
         ((GuardMemoryVectorChecker.memory_bounded_assumed_loop bounds loop,context),variables) in
       (match extract request.AffineNestCheckedCompiler.affine_requested_loop,extract candidate with
        | Result.Okk source,Result.Okk target ->
            let (before,_),_ = GuardMemoryExtractorProgress.memory_normalize_poly_program source in
            let expected,after = match evidence with
              | AffineNestCandidateEvidence.AffineIndexEvidence steps ->
                  let (after,_),_ = GuardMemoryAffineReindex.memory_affine_reindex_poly_program steps target in
                  before,after
              | AffineNestCandidateEvidence.AffineTilingEvidence witnesses ->
                  let (after,_),_ = GuardMemoryExtractorProgress.memory_normalize_poly_program target in
                  (match GuardMemoryExtractedTiling.memory_attach_tiling_instructions (nat (List.length context)) before after witnesses with
                   | Some attached -> List.map (GuardMemoryExtractedTiling.PL.current_view_pi (nat (List.length context))) attached,after
                   | None -> [],after) in
            let aligned,alarm_free = GuardMemoryDomainAlignment.memory_align_domains expected after in
            diagnostic (Printf.sprintf "GUARDCERT_AFFINE_EXTRACT source=%d target=%d aligned=%b alarm_free=%b"
              (List.length before) (List.length after) (aligned<>None) alarm_free)
        | Result.Err error,_ -> diagnostic ("GUARDCERT_AFFINE_EXTRACT source_error=" ^ error)
        | _,Result.Err error -> diagnostic ("GUARDCERT_AFFINE_EXTRACT target_error=" ^ error))
   | _ -> ());
  result
