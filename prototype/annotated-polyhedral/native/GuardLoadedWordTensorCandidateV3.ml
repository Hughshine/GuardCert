(* Untrusted source discovery. Exact source/leaf binding, private resources and
   canonical model are checked by the extracted loaded-word frontend factory. *)
module D = ClightTensorLoadedWordFactory
module S = ClightNestedConstantSite
let diagnostic = GuardTensorAffineRegionCandidate.diagnostic
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
let rec syntax depth source = if depth=0 then "..." else match source with
  | Clight.Sskip -> "skip" | Clight.Sset _ -> "set" | Clight.Sassign _ -> "store"
  | Clight.Ssequence (a,b) -> "seq("^syntax(depth-1)a^","^syntax(depth-1)b^")"
  | Clight.Sloop (a,b) -> "loop("^syntax(depth-1)a^","^syntax(depth-1)b^")"
  | Clight.Sifthenelse _ -> "if" | _ -> "other"
let rec expression = function
  | Clight.Etempvar _ -> "temp" | Clight.Econst_int _ -> "int"
  | Clight.Ederef (e,_) -> "load("^expression e^ ")"
  | Clight.Ebinop (op,a,b,_) ->
    let op=match op with Cop.Oadd -> "add"|Cop.Olt -> "lt"|_ -> "bin"in
    op^"("^expression a^","^expression b^")"
  | _ -> "other"
let describe _live pool source =
  try
    (match source with Clight.Sloop _ -> diagnostic("GUARDCERT_LOADED_WORD_INPUT "^syntax 9 source)|_ -> ());
    if GuardTensorAffineRegionCandidate.mode () = "disabled" then None else
    match strict_loop source with
    | Some (row,root,outer_body) ->
      diagnostic("GUARDCERT_LOADED_WORD_ROOT "^expression root^" reset="^string_of_bool(reset_loop outer_body<>None));
      (match root_header root,reset_loop outer_body with
       | Some (indexed,header,delta),Some (column,
           Clight.Ebinop (Cop.Oadd,Clight.Ederef
             (Clight.Ebinop (Cop.Oadd,Clight.Etempvar (child_header,_),Clight.Econst_int (offset,_),_),_),
             Clight.Econst_int (child_delta,_),_),component) when header=child_header ->
         (match reset_loop component,pool with
          | Some (iterator,Clight.Econst_int (upper,_),
              Clight.Ssequence (Clight.Sskip,(Clight.Sassign (Clight.Ederef (Clight.Ebinop
                (Cop.Oadd,Clight.Etempvar (pointer,_),index,_),_),rhs) as leaf))),
            (root_cache,_)::(child_cache,_)::(helper,_)::(row_cursor,_)::(row_limit,_)::
            (column_cursor,_)::(column_limit,_)::(component_cursor,_)::(component_limit,_)::(flag,_)::_ ->
            let shape = {
              S.ncs_row=row; ncs_column=column; ncs_iterator=iterator;
              ncs_root_cache=root_cache; ncs_child_cache=child_cache;
              ncs_child_helper=helper; ncs_component_helper=helper;
              ncs_upper=Integers.Int.signed upper; ncs_leaf=leaf;
              ncs_pointer=header; ncs_index=offset; ncs_delta=delta; ncs_child_delta=child_delta } in
            let cap = GuardTensorAffineRegionCandidate.integer
              (GuardTensorAffineRegionCandidate.configured "GUARDCERT_TENSOR_CAP" "32") in
            let description = {
              D.lwd_shape=shape; lwd_pointer=pointer; lwd_index=index; lwd_rhs=rhs;
              lwd_row_cursor=row_cursor; lwd_row_limit=row_limit;
              lwd_column_cursor=column_cursor; lwd_column_limit=column_limit;
              lwd_component_cursor=component_cursor; lwd_component_limit=component_limit;
              lwd_flag=flag; lwd_root_cap=cap; lwd_child_cap=cap } in
            diagnostic("GUARDCERT_LOADED_WORD_SOURCE indexed="^string_of_bool indexed);
            Some (indexed,description)
          | _ -> None)
       | _ -> None)
    | _ -> None
  with Invalid_argument _ | Failure _ | Stack_overflow -> None
