(* Diagnostic evaluation of the same pure extracted domain postpass that the
   actual proved machine compiler consumes. The adapter returns its reference
   candidate for the original affine/final checker, without a semantic override. *)
include GuardSelectedDoubleTreeSourcePolicies
module B = GuardMemoryDoubleTreePrunedCandidate.DoubleBodyPruning

let adapt intervals source raw =
  match GuardSelectedDoubleTreeSourcePolicies.adapt intervals source raw with
  | Result.Err reason -> Result.Err reason
  | Result.Okk (((reference,context),variables) as candidate) ->
      let bounds=List.map (fun (lower,upper)->{B.A.lower=lower;B.A.upper=upper}) intervals in
      let actual=B.prune bounds reference in
      (match !current_path with
       | None->()
       | Some path->
           emit (Filename.concat path "tree-runtime-pruned.loop") (statement "" actual);
           emit (Filename.concat path "tree-runtime-pruning.txt")
             (Printf.sprintf "changed=%b\nreference-check=pending\nactual-postpass=extracted-verified-function\n"
               (reference<>actual)));
      Result.Okk candidate
