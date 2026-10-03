(* Untrusted schedule input. Only the independently checked generated Loop
   can reach the guarded whole-program compiler. *)
let axis ordinal =
  let open GuardMemoryCandidate in function
  | Atom "ordinal" -> ([],GuardMemoryNumbers.import_integer (Z.of_int ordinal))
  | List [Atom "ordinal"; factor; bias] ->
    ([],GuardMemoryNumbers.import_integer (Z.add (Z.mul (integer factor) (Z.of_int ordinal)) (integer bias)))
  | List [Atom "affine"; List coefficients; bias] ->
    if List.length coefficients > 32 then invalid_arg "schedule coefficient limit";
    (List.map (fun value -> GuardMemoryNumbers.import_integer (integer value)) coefficients,
     GuardMemoryNumbers.import_integer (integer bias))
  | _ -> invalid_arg "schedule axis"

let instantiate instructions axes =
  if List.length instructions > 32 || List.length axes > 16 then invalid_arg "schedule size limit";
  List.mapi (fun ordinal _ -> List.map (axis ordinal) axes) instructions

let explicit schedules =
  let open GuardMemoryCandidate in
  if List.length schedules > 32 then invalid_arg "schedule site limit";
  List.mapi (fun ordinal schedule ->
    let axes=members schedule in
    if List.length axes > 16 then invalid_arg "schedule axis limit";
    List.map (axis ordinal) axes) schedules
