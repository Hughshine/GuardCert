(* This adapter proposes metadata for a retained loaded header. The extracted
   source, allocation, guard, dependence and backend checks validate its output. *)
let describe live pool source =
  try
    match source,List.rev pool with
    | Clight.Sloop
        (Clight.Ssequence
          (Clight.Ssequence (Clight.Sskip,
            Clight.Sifthenelse
              (Clight.Ebinop (Cop.Olt,Clight.Etempvar (iterator,_),
                Clight.Ederef (Clight.Etempvar (pointer,_),_),_),
               Clight.Sskip,Clight.Sbreak)),body),_),
      (cache,_)::rest ->
        let cached = ClightFrontendLoopProtocol.frontend_counted_loop iterator cache body in
        let usable_pool = List.rev rest in
        (match GuardAffineNestCandidate.describe live usable_pool cached with
         | None -> None
         | Some (parameters,proposal) ->
             let depth = 1 + List.length proposal.AffineNestGuardPackage.affine_proposed_remaining in
             let result,_ = List.nth usable_pool (4*depth) in
             let proposal = { proposal with AffineNestGuardPackage.affine_proposed_result = result } in
             ignore (GuardAffineNestCandidate.remember live pool (Some (parameters,proposal)));
             GuardAffineNestCandidate.diagnostic
               (Printf.sprintf "GUARDCERT_LOADED_AFFINE_SOURCE depth=%d" depth);
             Some ((parameters,proposal),pointer))
    | _ -> None
  with Invalid_argument _ | Failure _ | Stack_overflow -> None

let propose request = GuardAffineNestCandidate.propose_raw request
