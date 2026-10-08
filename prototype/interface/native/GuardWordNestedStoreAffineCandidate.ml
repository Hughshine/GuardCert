(* Ordinary metadata only. The extracted source/body/model checkers check every
   proposal against the actual Clight AST. No source-user proof callback. *)
module W = ClightWordNestedStoreFactory
module A = GuardMemoryAffineSourceExpressions
module D = ClightMultiTensorDataSource
module P = ClightMultiTensorDataPackage
module T = GuardMemoryDynamicTensorBackend
module V = GuardMemoryRuntime
let integer = GuardMemoryNumbers.import_integer
let signed word = GuardMemoryNumbers.export_integer (Integers.Int.signed word)
let rec nat = function 0 -> Datatypes.O | n -> Datatypes.S (nat (n-1))
let diagnostic text = if Sys.getenv_opt "GUARDCERT_TENSOR_DIAGNOSTICS" = Some "1" then
  prerr_endline text
let enabled () = Sys.getenv_opt "GUARDCERT_TENSOR_MODE" <> Some "disabled"
let configured variable fallback =
  let value=Option.value (Sys.getenv_opt variable) ~default:fallback in
  if String.length value>128 then invalid_arg "oversized loaded-family option";
  Z.of_string value
let unique values = List.fold_left (fun result id ->
  if List.mem id result then result else result@[id]) [] values
let rec flatten = function
  | Clight.Sskip -> []
  | Clight.Ssequence (a,b) -> flatten a @ flatten b
  | code -> [code]
let header = function
  | Clight.Ebinop (Cop.Oadd,Clight.Ederef (Clight.Etempvar (pointer,_),_),
      Clight.Econst_int (delta,_),_) -> pointer,delta
  | _ -> invalid_arg "loaded header requires explicit word offset"
let describe source = if not(enabled()) then None else try
  match ClightSignedExpressionProgress.checked_signed_expression_progress source with
  | None -> None
  | Some ((row,bound),outer_body) ->
    let pointer,delta=header bound in
    (match flatten outer_body with
     | [Clight.Sset (reset,Clight.Econst_int (zero,_));child] when zero=Integers.Int.zero ->
       (match ClightSignedExpressionProgress.checked_signed_expression_progress child with
        | Some ((column,child_bound),body) when column=reset ->
          let child_pointer,child_delta=header child_bound in
          let data={W.nws_row=row;W.nws_pointer=pointer;W.nws_delta=delta;
            W.nws_column=column;W.nws_child_pointer=child_pointer;
            W.nws_child_delta=child_delta;W.nws_body=body} in
          diagnostic (Printf.sprintf "GUARDCERT_LOADED_DESCRIPTION axes=2 stores=%d source-equality=%b"
            (List.length(flatten body)) (source=W.nws_source data));
          Some data
        | _ -> None)
     | _ -> None)
  with Invalid_argument _ | Failure _ | Stack_overflow -> None

let rec affine = function
  | Clight.Etempvar (id,ty) when ty=Ctypes.type_int32s -> A.MemorySourceTemp id
  | Clight.Econst_int (word,ty) when ty=Ctypes.type_int32s -> A.MemorySourceConstant(integer(signed word))
  | Clight.Ebinop(Cop.Oadd,a,b,_) -> A.MemorySourceAdd(affine a,affine b)
  | Clight.Ebinop(Cop.Osub,a,b,_) -> A.MemorySourceSub(affine a,affine b)
  | Clight.Ebinop(Cop.Omul,a,Clight.Econst_int(k,_),_) -> A.MemorySourceScale(integer(signed k),affine a)
  | Clight.Ebinop(Cop.Omul,Clight.Econst_int(k,_),a,_) -> A.MemorySourceScaleLeft(integer(signed k),affine a)
  | _ -> invalid_arg "non-affine coordinate"
let rec affine_reads = function
  | A.MemorySourceTemp id -> [id] | A.MemorySourceConstant _ -> []
  | A.MemorySourceAdd(a,b) | A.MemorySourceSub(a,b) -> affine_reads a @ affine_reads b
  | A.MemorySourceScale(_,a) | A.MemorySourceScaleLeft(_,a) -> affine_reads a
type stride = Constant of Z.t | Parameter of BinNums.positive
let horner = function
  | Clight.Ebinop(Cop.Oadd,Clight.Ebinop(Cop.Omul,a,Clight.Econst_int(k,_),_),b,_) ->
    [affine a;affine b],Constant(signed k)
  | Clight.Ebinop(Cop.Oadd,Clight.Ebinop(Cop.Omul,a,Clight.Etempvar(ld,_),_),b,_) ->
    [affine a;affine b],Parameter ld
  | _ -> invalid_arg "two-coordinate Horner layout required"
let access = function
  | Clight.Ederef(Clight.Ebinop(Cop.Oadd,Clight.Etempvar(pointer,_),index,_),_) ->
    let coordinates,stride=horner index in (pointer,coordinates),stride
  | _ -> invalid_arg "integer pointer plus affine index required"
type raw_value =
  | Word of Z.t | Temp of BinNums.positive
  | Load of (BinNums.positive * A.memory_source_affine list)
  | Add of raw_value*raw_value | Sub of raw_value*raw_value | Mul of raw_value*raw_value
let describe_cached source = if not(enabled()) then None else try
  let normalized=ClightLoopAdministrative.trim_loop_skips source in
  match ClightMultiTensorRegionFactory.multi_tensor_propose_nest
    (ClightStructuredProgress.progress_syntax_size normalized) normalized with
  | None -> None
  | Some nest ->
    let iterators=GuardMemoryRecursiveSource.memory_nest_iterators nest in
    let bounds=GuardMemoryRecursiveSource.memory_nest_bounds nest in
    if List.length iterators<>2 || List.length bounds<>2 then None else
    let statements=flatten(GuardMemoryRecursiveSource.memory_nest_leaf nest) in
    let (_,first_coordinates),stride=match statements with
      | Clight.Sassign(lhs,_)::_ -> access lhs
      | _ -> invalid_arg "assignment list required" in
    let parse_access expression =
      let cell,other=access expression in
      if other<>stride then invalid_arg "inconsistent physical layouts";
      cell in
    let rec raw = function
      | Clight.Econst_int(word,_) -> Word(signed word)
      | Clight.Etempvar(id,ty) when ty=Ctypes.type_int32s -> Temp id
      | Clight.Ederef _ as cell -> Load(parse_access cell)
      | Clight.Ebinop(Cop.Oadd,a,b,_) -> Add(raw a,raw b)
      | Clight.Ebinop(Cop.Osub,a,b,_) -> Sub(raw a,raw b)
      | Clight.Ebinop(Cop.Omul,a,b,_) -> Mul(raw a,raw b)
      | _ -> invalid_arg "unsupported value expression" in
    let assignments=List.map(function Clight.Sassign(lhs,rhs)->parse_access lhs,raw rhs
      | _ -> invalid_arg "non-assignment body")statements in
    let rec value_temps = function
      | Temp id -> [id] | Word _ | Load _ -> []
      | Add(a,b) | Sub(a,b) | Mul(a,b) -> value_temps a @ value_temps b in
    let rec coordinate_temps = function
      | Word _ | Temp _ -> [] | Load(_,coords) -> List.concat_map affine_reads coords
      | Add(a,b) | Sub(a,b) | Mul(a,b) -> coordinate_temps a @ coordinate_temps b in
    let coordinate_ids=unique(List.concat_map(fun ((_,coords),rhs)->
      List.concat_map affine_reads coords @ coordinate_temps rhs)assignments) in
    let dimension_ids=match stride with Constant _->[]|Parameter id->[id] in
    let scalars=unique(List.filter(fun id->not(List.mem id iterators))
      (coordinate_ids @ dimension_ids @ List.concat_map(fun (_,rhs)->value_temps rhs)assignments)) in
    let layout=iterators @ scalars in
    let position id =
      let rec find index=function
        | head::_ when head=id -> nat index
        | _::tail -> find(index+1)tail
        | [] -> invalid_arg "unbound value parameter" in find 0 layout in
    let data=List.map(fun (write,rhs)->
      let reads=ref [] in
      let rec value = function
        | Word word -> V.ConstantValue(integer word)
        | Temp id -> V.ParameterValue(position id)
        | Load cell -> let index=List.length !reads in reads:= !reads@[cell];V.LoadedValue(nat index)
        | Add(a,b) -> let a=value a in let b=value b in V.AddValue(a,b)
        | Sub(a,b) -> let a=value a in let b=value b in V.SubValue(a,b)
        | Mul(a,b) -> let a=value a in let b=value b in V.MulValue(a,b) in
      let rhs=value rhs in {D.mta_write=write;D.mta_reads= !reads;D.mta_value=rhs})assignments in
    let cap=configured "GUARDCERT_TENSOR_CAP" "8" in
    let count=integer Z.one,integer(Z.succ cap) in
    let stride_range=integer Z.one,integer(configured "GUARDCERT_TENSOR_STRIDE_HIGH" "1000") in
    let word_range=integer(Z.of_string "-2147483648"),integer(Z.of_string "2147483648") in
    let leading=match List.hd first_coordinates with
      | A.MemorySourceTemp id ->
        let rec find=function
          | (i,n)::_ when i=id -> n | _::tail -> find tail | [] -> List.hd bounds in
        find(List.combine iterators bounds)
      | _ -> List.hd bounds in
    let dimensions=match stride with
      | Constant extent -> if Z.sign extent<=0 then invalid_arg "nonpositive extent";
        [T.TensorDimensionTemp leading;T.TensorDimensionConstant(integer extent)]
      | Parameter ld -> [T.TensorDimensionTemp leading;T.TensorDimensionTemp ld] in
    let scalar_range id =
      if List.mem id dimension_ids then stride_range else if List.mem id coordinate_ids then
        integer(Z.neg cap),integer(Z.succ cap) else word_range in
    let dimension_profile=count :: (match stride with Constant _->[]|Parameter _->[stride_range]) in
    diagnostic(Printf.sprintf "GUARDCERT_LOADED_MODEL axes=2 assignments=%d arrays=%d scalars=%d"
      (List.length data)(List.length(unique(List.concat_map(fun d->
        fst d.D.mta_write::List.map fst d.D.mta_reads)data)))(List.length scalars));
    Some {P.mtr_dimensions=dimensions;P.mtr_scalars=scalars;P.mtr_assignments=data;
      P.mtr_cap=integer cap;P.mtr_profile=List.map(fun _->count)bounds @
        List.map scalar_range scalars @ dimension_profile}
  with Invalid_argument _ | Failure _ | Stack_overflow -> None
