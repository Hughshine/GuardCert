(* Header metadata is proposed through the existing cached affine recognizer.
   The extracted checker binds it back to the untouched compound source AST. *)
let describe live pool source =
  match source with
  | Clight.Sloop
      (Clight.Ssequence
        (Clight.Ssequence (Clight.Sskip,
          Clight.Sifthenelse
            (Clight.Ebinop (Cop.Olt,counter,
              Clight.Ebinop (Cop.Oadd,
                (Clight.Ederef (Clight.Etempvar (_,_),_) as loaded),
                Clight.Econst_int (delta,_),_),comparison_type),
             Clight.Sskip,Clight.Sbreak)),body),increment) ->
      let observation_source = Clight.Sloop
        (Clight.Ssequence
          (Clight.Ssequence (Clight.Sskip,
            Clight.Sifthenelse
              (Clight.Ebinop (Cop.Olt,counter,loaded,comparison_type),
               Clight.Sskip,Clight.Sbreak)),body),increment) in
      (match GuardLoadedAffineCandidate.describe live pool observation_source with
       | Some ((parameters,proposal),pointer) ->
           GuardAffineNestCandidate.diagnostic "GUARDCERT_LOADED_OFFSET_AFFINE_SOURCE";
           Some (((parameters,proposal),pointer),delta)
       | None -> None)
  | _ -> None

let propose request = GuardLoadedAffineCandidate.propose request
