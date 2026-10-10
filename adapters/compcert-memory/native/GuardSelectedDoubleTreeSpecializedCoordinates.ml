(* Original singleton cleanup precedes parameter specialization, so newly
   singleton tile binders remain available to the existing tiling witness.
   Adaptation remains an untrusted proposal checked by the actual compiler. *)
include GuardSelectedDoubleTreeResidualBounds
module Specialization = GuardMemoryDoubleParameterSpecialization.DoubleParameterSpecialization

let adapt intervals source ((raw,context),variables) =
  incr adaptations;
  verified_predicates:=0;cleared_floor_nodes:=0;
  try
    if List.length context<>List.length intervals then invalid_arg "source interval layout";
    let path=match !current_path with Some path->path | None->failwith "missing phase receipt" in
    emit (Filename.concat path "tree-source.loop") (statement "" (fst (fst source)));
    emit (Filename.concat path "tree-raw-generated.loop") (statement "" raw);
    let without_singletons,singletons=singleton_eliminate raw in
    let facts=Specialization.singleton_facts intervals in
    let specialized=if Sys.getenv_opt "GUARDCERT_PARAMETER_SPECIALIZATION"=Some "disabled"
      then without_singletons else Specialization.statement facts without_singletons in
    emit (Filename.concat path "tree-original-codegen.loop") (statement "" raw);
    emit (Filename.concat path "tree-specialized-codegen.loop") (statement "" specialized);
    emit (Filename.concat path "tree-parameter-specialization.txt")
      (Printf.sprintf "changed=%b\nproducer=extracted-verified-function\nknown-parameters=%s\norder=original-singleton-cleanup-before-specialization\nfinal-check=pending\n"
        (without_singletons<>specialized)
        (String.concat "," (List.map (function None->"unknown" | Some value->integer_text value) facts)));
    let recovered,translations=recover_points specialized in
    emit (Filename.concat path "tree-point-normalized.loop") (statement "" recovered);
    let proposed,reason=try
      let body,count=source_mixed_candidate intervals source in
      body,"source-mixed-box-points=" ^ string_of_int count
    with Invalid_argument _ | Not_found ->
      let body,count=coalesce_prefix recovered in
      body,"coalesced-prefixes=" ^ string_of_int count in
    emit (Filename.concat path "tree-coalesced.loop") (statement "" proposed);
    let generated,proposals=enclosing_bounds intervals proposed in
    let generated,moved=hoist_independent generated in
    let extraction=match E.extractor ((generated,context),variables) with
      | Result.Okk ((instructions,_),_)->"accepted points=" ^ string_of_int (List.length instructions)
      | Result.Err reason->"refused reason=" ^ reason in
    emit (Filename.concat path "tree-candidate-extraction.txt") (extraction ^ "\n");
    emit (Filename.concat path "tree-bounded-proposals.txt") proposals;
    emit (Filename.concat path "tree-generated.loop") (statement "" generated);
    emit (Filename.concat path "tree-normalization.txt")
      (Printf.sprintf "singletons=%d translations=%d %s hoisted=%d\nfinal-check=pending\n"
        singletons translations reason moved);
    let bounds=List.map (fun (lower,upper)->{B.A.lower=lower;B.A.upper=upper}) intervals in
    let residual_bounds=List.map (fun (lower,upper)->{R.A.lower=lower;R.A.upper=upper}) intervals in
    let pruned=B.prune bounds generated in
    let actual=F.factor_statement (R.residual_statement residual_bounds [] pruned) in
    emit (Filename.concat path "tree-runtime-pruned.loop") (statement "" pruned);
    emit (Filename.concat path "tree-runtime-residual.loop") (statement "" actual);
    emit (Filename.concat path "tree-runtime-residual.txt")
      (Printf.sprintf "changed=%b\nreference-check=pending\nactual-postpass=extracted-verified-function\n" (pruned<>actual));
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error->
    (match !current_path with Some path->emit (Filename.concat path "tree-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None->());
    Result.Err (Printexc.to_string error)
