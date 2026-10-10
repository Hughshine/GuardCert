(* Data-only proposals for the checked piece factory. Parameter constraints
   have already been encoded by the proved Loop guard and extractor. *)
include GuardSelectedDoublePieceModel

let adapt = GuardSelectedDoubleTreeSpecializedCoordinates.adapt

let propose model actual =
  try
    let (parents,context),variables=model in
    let (candidates,candidate_context),candidate_variables=actual in
    if context<>candidate_context || variables<>candidate_variables then invalid_arg "piece proposal declarations differ";
    let parameters=List.length context in
    let assignments=List.mapi (fun index candidate->
      let parent,source=List.mapi (fun index source->index,source) parents |>
        List.find (fun (_,source)->I.eqb source.P.pi_instr candidate.P.pi_instr) in
      let piece=propose parameters [] source candidate in
      (match !current_path with None->() | Some path->
        emit (Filename.concat path (Printf.sprintf "piece-proposal-%d.json" index))
          (Printf.sprintf "{\"piece\":%d,\"parent\":%d,\"source_depth\":%d,\"candidate_depth\":%d,\"source_domain\":%s,\"candidate_domain\":%s,\"embed\":%s,\"project\":%s,\"source_arguments\":%s,\"candidate_arguments\":%s,\"actual_schedule\":%s}\n"
            index parent (IO.nat_to_int source.P.pi_depth) (IO.nat_to_int candidate.P.pi_depth)
            (json_rows source.P.pi_poly) (json_rows candidate.P.pi_poly)
            (json_rows piece.PC.piece_embed) (json_rows piece.PC.piece_project)
            (json_rows source.P.pi_transformation) (json_rows candidate.P.pi_transformation)
            (json_rows candidate.P.pi_schedule)));
      parent,(candidate,piece)) candidates in
    let groups=List.mapi (fun parent _->List.filter_map
      (fun (id,item)->if id=parent then Some item else None) assignments) parents in
    if List.map fst (List.concat groups)<>candidates then invalid_arg "piece proposal static group order";
    let coverage=List.map2 (fun source group->coverage source.P.pi_poly
      (List.map (fun (_,piece)->PC.piece_image_domain piece) group) |> sequence_witness) parents groups in
    (match !current_path with None->() | Some path->
      emit (Filename.concat path "piece-proposal.txt")
        (Printf.sprintf "scope=untrusted-data-proposal\nsource-instructions=%d\ncandidate-pieces=%d\nproposal=available\n"
          (List.length parents) (List.length candidates)));
    Some (groups,coverage)
  with (Invalid_argument _ | Failure _ | Not_found | Sys_error _) as error->
    (match !current_path with None->() | Some path->
      emit (Filename.concat path "piece-proposal.txt")
        ("scope=untrusted-data-proposal\nproposal=refused reason=" ^ Printexc.to_string error ^ "\n"));
    None
