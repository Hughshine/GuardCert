(* Untrusted integer selection and data policies. The factory materializes only
   exact typed tests, validates the actual canonical source, and preserves the
   original AST as fallback. No semantic callback is supplied by this module. *)
include GuardTensorAffineRegionCandidate
let first left right = match left with Some _ -> left | None -> right ()
let rec literal source = match source with
  | Clight.Ssequence (left,right) | Clight.Sloop (left,right) -> first (literal left) (fun () -> literal right)
  | Clight.Sifthenelse (test,yes,no) ->
    (match test with
     | Clight.Ebinop (Cop.Olt,Clight.Etempvar (_,ty),Clight.Econst_int (upper,bound_ty),result_ty)
       when ty=Ctypes.type_int32s && bound_ty=Ctypes.type_int32s && result_ty=Ctypes.type_int32s -> Some upper
     | _ -> first (literal yes) (fun () -> literal no))
  | _ -> None
let choose source =
  if mode () = "disabled" then None else
  match literal source with
  | Some upper ->
    diagnostic ("GUARDCERT_TENSOR_LITERAL word=" ^ Z.to_string
      (GuardMemoryNumbers.export_integer (Integers.Int.signed upper)));
    Some (if mode () = "wrong-literal" then Integers.Int.add upper Integers.Int.one else upper)
  | None -> None
let propose instructions =
  if mode () = "wrong-literal" then Some (R.TensorRegionMapped
    (GuardMemoryScalarLoops.memory_scalar_rectangle (nat 0) (nat 3) (nat 2) instructions,[]))
  else GuardTensorAffineRegionCandidate.propose instructions
