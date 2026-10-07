(* Untrusted discovery and proposal. The extracted factory checks the actual
   source AST, resources, model, candidate evidence, and lowering result. *)
module Shape = ClightNestedConstantSite
let diagnostic = GuardAffineNestCandidate.diagnostic

let rec syntax depth source = if depth=0 then "..." else match source with
  | Clight.Sskip -> "skip"
  | Clight.Sset _ -> "set"
  | Clight.Ssequence (first,second) -> "seq("^syntax(depth-1)first^","^syntax(depth-1)second^")"
  | Clight.Sloop (first,second) -> "loop("^syntax(depth-1)first^","^syntax(depth-1)second^")"
  | Clight.Sifthenelse _ -> "if"
  | _ -> "other"

let strict_loop = function
  | Clight.Sloop (Clight.Ssequence
      (Clight.Ssequence (Clight.Sskip,Clight.Sifthenelse
        (Clight.Ebinop (Cop.Olt,Clight.Etempvar (iterator,_),bound,_),Clight.Sskip,Clight.Sbreak)),body),_) ->
      Some (iterator,bound,body)
  | _ -> None

let reset_loop = function
  | Clight.Ssequence (Clight.Ssequence (Clight.Sskip,
      Clight.Sset (iterator,Clight.Econst_int (zero,_))),loop)
      when Integers.Int.eq zero Integers.Int.zero ->
      (match strict_loop loop with
       | Some (counter,bound,body) when counter=iterator -> Some (counter,bound,body)
       | _ -> None)
  | _ -> None

let root_header = function
  | Clight.Ebinop (Cop.Oadd,Clight.Ederef (Clight.Etempvar (pointer,_),_),Clight.Econst_int (delta,_),_) ->
      Some (false,pointer,delta)
  | Clight.Ebinop (Cop.Oadd,Clight.Ederef
      (Clight.Ebinop (Cop.Oadd,Clight.Etempvar (pointer,_),Clight.Econst_int (zero,_),_),_),
      Clight.Econst_int (delta,_),_) when Integers.Int.eq zero Integers.Int.zero ->
      Some (true,pointer,delta)
  | _ -> None

let describe live pool source =
  try
    (match source with Clight.Sloop _ -> diagnostic("GUARDCERT_NESTED_INPUT "^syntax 6 source) | _ -> ());
    match strict_loop source with
    | Some (row,root,outer_body) ->
      (match root_header root,reset_loop outer_body with
       | Some (indexed,pointer,delta),Some (column,
           Clight.Ebinop (Cop.Oadd,Clight.Ederef
             (Clight.Ebinop (Cop.Oadd,Clight.Etempvar (child_pointer,_),Clight.Econst_int (index,_),_),_),
             Clight.Econst_int (child_delta,_),_),child_body) when pointer=child_pointer ->
         (match reset_loop child_body,List.rev pool with
          | Some (iterator,Clight.Econst_int (upper,_),leaf),
            (root_cache,_)::(child_cache,_)::(child_helper,_)::(component_helper,_)::rest ->
            let shape = {
              Shape.ncs_row=row; ncs_column=column; ncs_iterator=iterator;
              ncs_root_cache=root_cache; ncs_child_cache=child_cache;
              ncs_child_helper=child_helper; ncs_component_helper=component_helper;
              ncs_upper=Integers.Int.signed upper; ncs_leaf=leaf;
              ncs_pointer=pointer; ncs_index=index; ncs_delta=delta; ncs_child_delta=child_delta } in
            let usable_pool=List.rev rest in
            let model=Shape.ncs_model shape in
            let policy={ (GuardAffineNestCandidate.range_policy ()) with
              AffineNestRangeProposal.affine_policy_root_floor=GuardAffineNestCandidate.integer 0 } in
            (match AffineNestRangeProposal.affine_source_range_proposal policy
                (Shape.ncs_package_live source live shape) usable_pool model with
             | Some (parameters,proposal) ->
               let depth=1+List.length proposal.AffineNestGuardPackage.affine_proposed_remaining in
               let result,_=List.nth usable_pool (4*depth) in
               let proposal={ proposal with AffineNestGuardPackage.affine_proposed_result=result } in
               let exact=ClightSyntaxEquality.statement_eq source(ClightNestedFrontendRegion.ncs_frontend_source indexed shape) in
               let allocated=List.map fst pool in
               let checked=ClightNestedConstantMultiSite.check_ncs_multi_site
                 (Shape.ncs_original shape)parameters live allocated proposal shape<>None in
               diagnostic(Printf.sprintf "GUARDCERT_NESTED_SOURCE indexed=%b exact=%b checked=%b depth=%d" indexed exact checked depth);
               Some (((indexed,parameters),proposal),shape)
             | None -> diagnostic "GUARDCERT_NESTED_MODEL_PROPOSAL_REFUSED"; None)
          | _ -> None)
       | _ -> None)
    | _ -> None
  with Invalid_argument _ | Failure _ | Stack_overflow -> None

let propose request = GuardAffineNestCandidate.propose_raw request
