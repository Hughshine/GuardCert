(* Inspect the same extracted pure postpasses consumed by the actual proved
   compiler. Return the reference to its existing final polyhedral checker. *)
include GuardSelectedDoubleTreeSourcePolicies
module B = GuardMemoryDoubleTreePrunedCandidate.DoubleBodyPruning
module R = GuardMemoryDoubleTreeResidualCandidate.DoubleResidual
module F = GuardMemoryDoubleTreeResidualCandidate.DoubleAdjacent

let adapt intervals source raw =
  match GuardSelectedDoubleTreeSourcePolicies.adapt intervals source raw with
  | Result.Err reason -> Result.Err reason
  | Result.Okk (((reference,context),variables) as candidate) ->
      let bounds=List.map (fun (lower,upper)->{B.A.lower=lower;B.A.upper=upper}) intervals in
      let residual_bounds=List.map (fun (lower,upper)->{R.A.lower=lower;R.A.upper=upper}) intervals in
      let pruned=B.prune bounds reference in
      let actual=F.factor_statement (R.residual_statement residual_bounds [] pruned) in
      (match !current_path with
       | None->()
       | Some path->
           emit (Filename.concat path "tree-runtime-pruned.loop") (statement "" pruned);
           emit (Filename.concat path "tree-runtime-residual.loop") (statement "" actual);
           emit (Filename.concat path "tree-runtime-residual.txt")
             (Printf.sprintf "changed=%b\nreference-check=pending\nactual-postpass=extracted-verified-function\n"
               (pruned<>actual)));
      Result.Okk candidate
