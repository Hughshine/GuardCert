(* Mutation policies return data to the actual proved factory. They do not
   decide acceptance and cannot bypass its source/candidate extraction checks. *)
include GuardSelectedDoublePieceProducer

let propose source candidate =
  match GuardSelectedDoublePieceProducer.propose source candidate with
  | None->None
  | Some (groups,coverage) as original->
    try
      let first=List.hd groups in
      let instruction,piece=List.hd first in
      let replace items=Some (replace_head items groups,coverage) in
      match Sys.getenv_opt "GUARDCERT_PIECE_POLICY" with
      | None | Some "valid"->original
      | Some "refuse"->None
      | Some "omit"->replace (List.tl first)
      | Some "duplicate"->replace ((instruction,piece)::first)
      | Some "prefix"->replace ((instruction,{piece with PC.piece_embed=mutate_prefix piece.PC.piece_embed})::List.tl first)
      | Some "arguments"->replace (({instruction with P.pi_transformation=mutate_bias instruction.P.pi_transformation},piece)::List.tl first)
      | Some "instruction"->
        let (parents,_),_=source in
        let other=List.find (fun pi->not (I.eqb pi.P.pi_instr instruction.P.pi_instr)) parents in
        replace (({instruction with P.pi_instr=other.P.pi_instr},piece)::List.tl first)
      | Some _->None
    with Invalid_argument _ | Failure _ | Not_found->None
