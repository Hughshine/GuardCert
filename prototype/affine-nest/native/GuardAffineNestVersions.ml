(* Range profiles are proposals; each stage checks its complete current source. *)
let describe_expanded_single_iteration live pool source =
  let result = try
    let policy = { (GuardAffineNestCandidate.range_policy ()) with
      AffineNestRangeProposal.affine_policy_root_floor = GuardAffineNestCandidate.integer 0;
      AffineNestRangeProposal.affine_policy_root_cap = GuardAffineNestCandidate.integer 1;
      AffineNestRangeProposal.affine_policy_bound_lower =
        GuardAffineNestCandidate.configured_integer "GUARDCERT_AFFINE_VERSION_BOUND_LOW" "-12";
      AffineNestRangeProposal.affine_policy_bound_upper =
        GuardAffineNestCandidate.configured_integer "GUARDCERT_AFFINE_VERSION_BOUND_HIGH" "13" } in
    AffineNestMultiProposal.affine_reserve_multi_scans
      (AffineNestRangeProposal.affine_source_range_proposal policy) live pool source
    with Invalid_argument _ | Failure _ | Stack_overflow -> None in
  GuardAffineNestCandidate.remember live pool result

let describes () =
  if Sys.getenv_opt "GUARDCERT_AFFINE_CONDITION_SEARCH" = Some "disabled"
  then [GuardAffineNestCandidate.describe]
  else [GuardAffineNestCandidate.describe; describe_expanded_single_iteration]
