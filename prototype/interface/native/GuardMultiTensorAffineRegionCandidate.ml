(* Untrusted recognition of actual three-axis Horner assignment lists.
   All metadata, source equality, guards and candidates are rechecked by Rocq
   code. No source/model or simulation callback is supplied here. *)
module A = GuardMemoryAffineSourceExpressions
module D = ClightMultiTensorDataSource
module P = ClightMultiTensorDataPackage
module V = GuardMemoryRuntime
module T = GuardMemoryDynamicTensorBackend
let rec nat = function 0 -> Datatypes.O | n -> Datatypes.S (nat (n-1))
let integer = GuardMemoryNumbers.import_integer
let signed = fun word -> GuardMemoryNumbers.export_integer (Integers.Int.signed word)
let diagnostic text = if Sys.getenv_opt "GUARDCERT_TENSOR_DIAGNOSTICS" = Some "1" then prerr_endline text
let configured variable fallback =
  let value = Option.value (Sys.getenv_opt variable) ~default:fallback in
  if String.length value > 128 then invalid_arg "oversized multi-tensor option";
  Z.of_string value
let unique values = List.fold_left (fun acc value -> if List.mem value acc then acc else acc@[value]) [] values
let rec affine = function
  | Clight.Etempvar (id,ty) when ty=Ctypes.type_int32s -> A.MemorySourceTemp id
  | Clight.Econst_int (word,ty) when ty=Ctypes.type_int32s -> A.MemorySourceConstant (integer (signed word))
  | Clight.Ebinop (Cop.Oadd,a,b,_) -> A.MemorySourceAdd (affine a,affine b)
  | Clight.Ebinop (Cop.Osub,a,b,_) -> A.MemorySourceSub (affine a,affine b)
  | Clight.Ebinop (Cop.Omul,a,Clight.Econst_int (k,_),_) -> A.MemorySourceScale (integer (signed k),affine a)
  | Clight.Ebinop (Cop.Omul,Clight.Econst_int (k,_),a,_) -> A.MemorySourceScaleLeft (integer (signed k),affine a)
  | _ -> invalid_arg "coordinate outside affine source syntax"
let rec affine_reads = function
  | A.MemorySourceTemp id -> [id] | A.MemorySourceConstant _ -> []
  | A.MemorySourceAdd (a,b) | A.MemorySourceSub (a,b) -> affine_reads a @ affine_reads b
  | A.MemorySourceScale (_,a) | A.MemorySourceScaleLeft (_,a) -> affine_reads a
let horner = function
  | Clight.Ebinop (Cop.Oadd,
      Clight.Ebinop (Cop.Omul,
        Clight.Ebinop (Cop.Oadd,Clight.Ebinop (Cop.Omul,a,Clight.Etempvar (ld,_),_),b,_),
        Clight.Econst_int (extent,_),_),c,_) ->
    [affine a;affine b;affine c],ld,signed extent
  | _ -> invalid_arg "index outside three-axis Horner syntax"
type raw_value =
  | Word of Z.t | Temp of BinNums.positive | Load of (BinNums.positive * A.memory_source_affine list)
  | Add of raw_value*raw_value | Sub of raw_value*raw_value | Mul of raw_value*raw_value
let rec flatten = function
  | Clight.Sskip -> []
  | Clight.Ssequence (a,b) -> flatten a @ flatten b
  | statement -> [statement]
let access = function
  | Clight.Ederef (Clight.Ebinop (Cop.Oadd,Clight.Etempvar (pointer,_),index,_),_) ->
    let coords,ld,extent = horner index in (pointer,coords),ld,extent
  | _ -> invalid_arg "access outside integer pointer plus Horner index"
let describe source =
  try
    if Sys.getenv_opt "GUARDCERT_TENSOR_MODE" = Some "disabled" then None else
    let normalized = ClightLoopAdministrative.trim_loop_skips source in
    match ClightMultiTensorRegionFactory.multi_tensor_propose_nest
      (ClightStructuredProgress.progress_syntax_size normalized) normalized with
    | None -> None
    | Some nest ->
      let iterators = GuardMemoryRecursiveSource.memory_nest_iterators nest in
      let bounds = GuardMemoryRecursiveSource.memory_nest_bounds nest in
      if List.length iterators<>3 || List.length bounds<>3 then None else
      let statements = flatten (GuardMemoryRecursiveSource.memory_nest_leaf nest) in
      let first = match statements with Clight.Sassign (lhs,_)::_ -> access lhs
        | _ -> invalid_arg "assignment list required" in
      let (_,first_coords),ld,extent = first in
      if Z.sign extent<=0 then invalid_arg "positive final layout extent required";
      let parse_access expression =
        let cell,stride,last = access expression in
        if stride<>ld || not (Z.equal last extent) then invalid_arg "inconsistent layouts";
        cell in
      let rec raw = function
        | Clight.Econst_int (word,_) -> Word (signed word)
        | Clight.Etempvar (id,ty) when ty=Ctypes.type_int32s -> Temp id
        | Clight.Ederef _ as expression -> Load (parse_access expression)
        | Clight.Ebinop (Cop.Oadd,a,b,_) -> Add (raw a,raw b)
        | Clight.Ebinop (Cop.Osub,a,b,_) -> Sub (raw a,raw b)
        | Clight.Ebinop (Cop.Omul,a,b,_) -> Mul (raw a,raw b)
        | _ -> invalid_arg "RHS outside integer value-expression syntax" in
      let assignments = List.map (function
        | Clight.Sassign (lhs,rhs) -> parse_access lhs,raw rhs
        | _ -> invalid_arg "non-assignment body") statements in
      let rec coordinate_reads = function
        | Word _ | Temp _ -> []
        | Load (_,coords) -> List.concat_map affine_reads coords
        | Add (a,b) | Sub (a,b) | Mul (a,b) ->
          coordinate_reads a @ coordinate_reads b in
      let coordinate_ids = unique (List.concat_map (fun ((_,coords),rhs) ->
        List.concat_map affine_reads coords @ coordinate_reads rhs) assignments) in
      let all_ids = ref [ld] in
      let rec temps = function
        | Temp id -> all_ids:= !all_ids@[id]
        | Add (a,b) | Sub (a,b) | Mul (a,b) -> temps a;temps b
        | _ -> () in
      List.iter (fun (_,rhs) -> temps rhs) assignments;
      let scalars = unique (List.filter (fun id -> not (List.mem id iterators)) (coordinate_ids @ !all_ids)) in
      let layout = iterators @ scalars in
      let position id =
        let rec find index = function
          | head::_ when head=id -> nat index
          | _::rest -> find (index+1) rest
          | [] -> invalid_arg "unbound source parameter" in find 0 layout in
      let data = List.map (fun (write,rhs) ->
        let reads=ref [] in
        let rec value = function
          | Word word -> V.ConstantValue (integer word)
          | Temp id -> V.ParameterValue (position id)
          | Load cell -> let index=List.length !reads in reads:= !reads@[cell];V.LoadedValue (nat index)
          | Add (a,b) -> let a=value a in let b=value b in V.AddValue (a,b)
          | Sub (a,b) -> let a=value a in let b=value b in V.SubValue (a,b)
          | Mul (a,b) -> let a=value a in let b=value b in V.MulValue (a,b) in
        let rhs=value rhs in {D.mta_write=write;D.mta_reads= !reads;D.mta_value=rhs}) assignments in
      let cap=configured "GUARDCERT_TENSOR_CAP" "8" in
      let stride_high=configured "GUARDCERT_TENSOR_STRIDE_HIGH" "1000" in
      let range a b=integer a,integer b in
      let count=range Z.one (Z.succ cap) and stride=range Z.one stride_high in
      let leading = match List.hd first_coords with
        | A.MemorySourceTemp id ->
          let rec find iters counts = match iters,counts with
            | i::_,n::_ when i=id -> n
            | _::is,_::ns -> find is ns
            | _ -> List.hd bounds in find iterators bounds
        | _ -> List.hd bounds in
      let dimensions=[T.TensorDimensionTemp leading;T.TensorDimensionTemp ld;
        T.TensorDimensionConstant (integer extent)] in
      let scalar_profile id = if id=ld then stride else if List.mem id coordinate_ids then
        range (Z.neg cap) (Z.succ cap) else range (Z.of_string "-2147483648") (Z.of_string "2147483648") in
      diagnostic (Printf.sprintf "GUARDCERT_MULTI_DESCRIPTION axes=3 assignments=%d arrays=%d scalars=%d"
        (List.length data) (List.length (unique (List.concat_map (fun d ->
          fst d.D.mta_write :: List.map fst d.D.mta_reads) data))) (List.length scalars));
      Some {P.mtr_dimensions=dimensions;P.mtr_scalars=scalars;P.mtr_assignments=data;P.mtr_cap=integer cap;
        P.mtr_profile=List.map (fun _->count) bounds @ List.map scalar_profile scalars @ [count;stride]}
  with Invalid_argument _ | Failure _ | Stack_overflow -> None
