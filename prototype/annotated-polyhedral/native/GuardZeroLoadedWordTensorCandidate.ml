(* Untrusted scalar discovery only. The extracted factory checks the complete
   RMW syntax, scalar stability, source binding, and allocated private names. *)
let describe live pool source =
  match GuardLoadedWordTensorCandidateV3.describe live pool source with
  | Some (indexed,description) ->
    (match description.ClightTensorLoadedWordFactory.lwd_rhs with
     | Clight.Ebinop (Cop.Oadd,Clight.Ederef _,Clight.Etempvar (alpha,_),_) ->
       Some (indexed,(description,alpha))
     | _ -> None)
  | None -> None
