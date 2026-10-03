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

(* Coordinate schedules use source metadata supplied by the checked package.
   The context prefix can contain unused dimensions and parameters; every
   resulting candidate is checked independently. *)
let rec natural_size = function
  | Datatypes.O -> 0
  | Datatypes.S rest -> 1 + natural_size rest

let coordinate_axis dimensions arity syntax =
  let open GuardMemoryCandidate in
  match syntax with
  | List [Atom (("coordinate" | "negative-coordinate") as direction); position] ->
      let position = small position in
      if position >= dimensions || dimensions > 16 || arity > 32
      then invalid_arg "coordinate schedule axis";
      let coefficients = List.init arity (fun _ -> Atom "0") @
        List.init dimensions (fun index -> Atom (if index=position
          then (if direction="negative-coordinate" then "-1" else "1") else "0")) in
      List [Atom "affine"; List coefficients; Atom "0"]
  | _ -> syntax

let instantiate dimensions arity instructions axes =
  if List.length instructions > 32 || List.length axes > 16 then invalid_arg "schedule size limit";
  let axes = List.map (coordinate_axis dimensions arity) axes in
  List.mapi (fun ordinal _ -> List.map (axis ordinal) axes) instructions

let explicit schedules =
  let open GuardMemoryCandidate in
  if List.length schedules > 32 then invalid_arg "schedule site limit";
  List.mapi (fun ordinal schedule ->
    let axes=members schedule in
    if List.length axes > 16 then invalid_arg "schedule axis limit";
    List.map (axis ordinal) axes) schedules
