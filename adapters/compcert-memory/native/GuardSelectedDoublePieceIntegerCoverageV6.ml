(* Diagnostic data-only successor. It returns the original proposal unchanged;
   the compiler still runs its own extracted checks before installation. *)
include GuardSelectedDoublePieceIntegerCoverageV5

let propose model actual =
  match GuardSelectedDoublePieceIntegerCoverageV5.propose model actual with
  | None -> None
  | Some (groups,witnesses) as answer ->
      let (parents,context),variables=model in
      let count=nat (List.length context) in
      let report label action =
        Printf.eprintf "GUARDCERT_PIECE_CHECK start=%s\n%!" label;
        let start=Unix.gettimeofday () in
        let accepted=checked_bool (action ()) in
        Printf.eprintf "GUARDCERT_PIECE_CHECK end=%s accepted=%b seconds=%.6f\n%!"
          label accepted (Unix.gettimeofday () -. start);
        accepted in
      let families=List.map2 (fun (index,source) (group,witness)->
        let prefix=Printf.sprintf "parent-%d" index in
        let actions=report (prefix ^ "-actions") (fun ()->Q.Single.check_single_actions count source group) in
        let width=nat (List.length context + IO.nat_to_int source.P.pi_depth) in
        let coordinates=Q.Single.single_coordinates group in
        let maps=report (prefix ^ "-coordinates") (fun ()->Q.Single.S.F.K.check_coordinate_family width source.P.pi_poly coordinates) in
        let images=List.map PC.piece_image_domain coordinates in
        let cover=report (prefix ^ "-cover") (fun ()->Q.Single.S.F.D.check_cover source.P.pi_poly images witness) in
        let disjoint=report (prefix ^ "-disjoint") (fun ()->Q.Single.S.F.D.check_disjoint_family images) in
        actions && maps && cover && disjoint)
        (List.mapi (fun index source->index,source) parents) (List.combine groups witnesses) in
      if List.for_all Fun.id families then
        ignore (report "actual-order" (fun ()->GuardMemoryDoublePolyhedral.validate_double_equivalence
          ((Q.sequence_target parents groups,context),variables) actual));
      answer
