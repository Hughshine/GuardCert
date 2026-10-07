(* Untrusted policies: infer descriptors from a three-axis Horner RMW AST and
   suggest schedules. The extracted factory rechecks the entire AST, metadata,
   condition compiler, dependence certificate and lowering. *)
module P = ClightTensorRegionPackage
module R = ClightTensorRegionPreservation
module L = GuardMemoryLoops.L
let rec nat = function 0 -> Datatypes.O | amount -> Datatypes.S (nat (amount-1))
let integer value = GuardMemoryNumbers.import_integer value
let small value = integer (Z.of_int value)
let mode () = match Sys.getenv_opt "GUARDCERT_TENSOR_MODE" with Some value -> value | None -> "interchange"
let diagnostic text = if Sys.getenv_opt "GUARDCERT_TENSOR_DIAGNOSTICS" = Some "1" then prerr_endline text
let configured variable fallback =
  let text = match Sys.getenv_opt variable with Some value -> value | None -> fallback in
  if String.length text > 128 then invalid_arg "tensor policy integer";
  Z.of_string text
let describe source =
  try if mode () = "disabled" then None else
    let normalized = ClightLoopAdministrative.trim_loop_skips source in
    match P.tensor_propose_nest (ClightStructuredProgress.progress_syntax_size normalized) normalized with
    | Some nest ->
      (match GuardMemoryRecursiveSource.memory_nest_iterators nest,
         GuardMemoryRecursiveSource.memory_nest_bounds nest,GuardMemoryRecursiveSource.memory_nest_leaf nest with
       | [i;j;k],[n;_columns;_components],
         Clight.Sassign ((Clight.Ederef (Clight.Ebinop (Cop.Oadd,Clight.Etempvar (pointer,_),index,_),_) as cell),
           Clight.Ebinop (Cop.Oadd,read,Clight.Etempvar (alpha,_),_)) when cell=read ->
         (match index with
          | Clight.Ebinop (Cop.Oadd,
              Clight.Ebinop (Cop.Omul,
                Clight.Ebinop (Cop.Oadd,
                  Clight.Ebinop (Cop.Omul,Clight.Etempvar (ii,_),Clight.Etempvar (ld,_),_),
                  Clight.Etempvar (jj,_),_),Clight.Econst_int (extent,_),_),Clight.Etempvar (kk,_),_)
              when i=ii && j=jj && k=kk ->
            let cap = configured "GUARDCERT_TENSOR_CAP" "32" in
            let stride_high = configured "GUARDCERT_TENSOR_STRIDE_HIGH" "1000" in
            let extent = GuardMemoryNumbers.export_integer (Integers.Int.signed extent) in
            let range lower upper = integer lower,integer upper in
            let count = range Z.one (Z.succ cap) in
            let stride = range Z.one stride_high in
            let coordinates = List.map (fun id -> GuardMemoryAffineSourceExpressions.MemorySourceTemp id) [i;j;k] in
            diagnostic "GUARDCERT_TENSOR_DESCRIPTION depth=3 horner-rmw";
            Some {
              P.tensor_region_dimensions = [GuardMemoryDynamicTensorBackend.TensorDimensionTemp n;
                GuardMemoryDynamicTensorBackend.TensorDimensionTemp ld;
                GuardMemoryDynamicTensorBackend.TensorDimensionConstant (integer extent)];
              P.tensor_region_scalars = [ld;alpha];
              P.tensor_region_pointer = pointer; P.tensor_region_array = pointer;
              P.tensor_region_write = coordinates; P.tensor_region_reads = [coordinates];
              P.tensor_region_value = GuardMemoryRuntime.AddValue
                (GuardMemoryRuntime.LoadedValue (nat 0),GuardMemoryRuntime.ParameterValue (nat 4));
              P.tensor_region_cap = integer cap;
              P.tensor_region_profile = [count;count;range Z.one (Z.succ extent);stride;
                range (Z.of_string "-2147483648") (Z.of_string "2147483648");count;stride]
            }
          | _ -> None)
       | _ -> None)
    | None -> None
  with Invalid_argument _ | Failure _ | Stack_overflow -> None

let interchange instructions =
  let arguments = List.map (fun index -> L.Var (nat index)) [1;2;0;6;7] in
  let body = L.Seq (List.fold_right (fun instruction tail -> L.SCons (L.Instr (instruction,arguments),tail)) instructions L.SNil) in
  L.Loop (L.Constant (small 0),L.Var (nat 1),
    L.Loop (L.Constant (small 0),L.Var (nat 1),
      L.Loop (L.Constant (small 0),L.Var (nat 4),body)))
let propose instructions =
  diagnostic ("GUARDCERT_TENSOR_REQUEST mode=" ^ mode ());
  match mode () with
  | "identity" -> Some (R.TensorRegionMapped
      (GuardMemoryScalarLoops.memory_scalar_rectangle (nat 0) (nat 3) (nat 2) instructions,[]))
  | "interchange" -> Some (R.TensorRegionMapped
      (interchange instructions,[GuardMemoryAffineReindex.MemoryReindexSwap (nat 0)]))
  | "wrong-reindex" -> Some (R.TensorRegionMapped (interchange instructions,[]))
  | "tile-2-3" -> Some (R.TensorRegionTiled (small 2,small 3))
  | "zero-tile" -> Some (R.TensorRegionTiled (small 0,small 3))
  | _ -> None
