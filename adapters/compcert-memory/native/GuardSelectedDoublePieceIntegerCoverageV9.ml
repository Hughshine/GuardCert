(* Data-only candidate proposal. The generated runtime simplification is itself
   an extracted verified service; installation checks the actual returned tree. *)
include GuardSelectedDoublePieceIntegerCoverageV5

let adapt intervals source raw =
  match GuardSelectedDoublePieceQuotients.adapt intervals source raw with
  | Result.Err _ as refused -> refused
  | Result.Okk ((generated,context),variables) ->
      let bounds=List.map (fun (lower,upper)->{B.A.lower=lower;B.A.upper=upper}) intervals in
      let actual=B.prune bounds generated in
      (match !current_path with None->() | Some path->
        emit (Filename.concat path "tree-checked-runtime-candidate.loop") (statement "" actual);
        emit (Filename.concat path "tree-checked-runtime-candidate.txt")
          (Printf.sprintf "scope=untrusted-candidate-data\nchanged=%b\nactual-model-extracted-from-returned-tree=true\nfinal-check=pending\n" (actual<>generated)));
      Result.Okk ((actual,context),variables)
