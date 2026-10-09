(* Untrusted proposals on the actual generated Loop. Recover source point
   coordinates from instruction arguments; the existing final candidate
   checker, progress proof and Clight factory decide whether to install them. *)
include GuardSelectedDoubleAdaptiveTiledCandidate
module Coefficients = Map.Make (Int)

let coefficients_add first second = Coefficients.merge (fun _ a b ->
  let value = Z.add (Option.value a ~default:Z.zero) (Option.value b ~default:Z.zero) in
  if Z.equal value Z.zero then None else Some value) first second

let rec linear = function
  | L.Constant value -> Some (Coefficients.empty, GuardMemoryNumbers.export_integer value)
  | L.Var index -> Some (Coefficients.singleton (GuardOpenScopDoubleIO.nat_to_int index) Z.one, Z.zero)
  | L.Sum (first, second) -> (match linear first, linear second with
      | Some (a, x), Some (b, y) -> Some (coefficients_add a b, Z.add x y)
      | _ -> None)
  | L.Mult (factor, value) -> (match linear value with
      | None -> None
      | Some (coefficients, constant) ->
          let factor = GuardMemoryNumbers.export_integer factor in
          Some (Coefficients.filter (fun _ value -> not (Z.equal value Z.zero))
            (Coefficients.map (Z.mul factor) coefficients), Z.mul factor constant))
  | _ -> None

let expression (coefficients, constant) =
  let terms = Coefficients.bindings coefficients |> List.map (fun (index, coefficient) ->
    let variable = L.Var (nat index) in
    if Z.equal coefficient Z.one then variable else L.Mult (integer coefficient, variable)) in
  let terms = if Z.equal constant Z.zero then terms else terms @ [L.Constant (integer constant)] in
  match terms with
  | [] -> L.Constant (small 0)
  | first :: rest -> List.fold_left (fun first second -> L.Sum (first, second)) first rest

let normalize value = match linear value with Some form -> expression form | None -> value
let add first second = normalize (L.Sum (first, second))
let negate value = normalize (L.Mult (small (-1), value))
let subtract first second = add first (negate second)
let form_equal (a, x) (b, y) = Coefficients.equal Z.equal a b && Z.equal x y

let rec lift_by count = function
  | L.Constant _ as value -> value
  | L.Var index -> L.Var (nat (GuardOpenScopDoubleIO.nat_to_int index + count))
  | L.Sum (a,b) -> add (lift_by count a) (lift_by count b)
  | L.Mult (factor,value) -> normalize (L.Mult (factor,lift_by count value))
  | L.Div (value, divisor) -> L.Div (lift_by count value, divisor)
  | L.Mod (value, divisor) -> L.Mod (lift_by count value, divisor)
  | L.Max (a,b) -> L.Max (lift_by count a,lift_by count b)
  | L.Min (a,b) -> L.Min (lift_by count a,lift_by count b)

let rec substitute_expression remove cutoff replacement = function
  | L.Constant _ as value -> value
  | L.Var index as value ->
      let index = GuardOpenScopDoubleIO.nat_to_int index in
      if index = cutoff then lift_by cutoff replacement
      else if remove && index > cutoff then L.Var (nat (index - 1)) else value
  | L.Sum (a,b) -> add (substitute_expression remove cutoff replacement a)
      (substitute_expression remove cutoff replacement b)
  | L.Mult (factor,value) -> normalize (L.Mult (factor,substitute_expression remove cutoff replacement value))
  | L.Div (value,divisor) -> L.Div (substitute_expression remove cutoff replacement value,divisor)
  | L.Mod (value,divisor) -> L.Mod (substitute_expression remove cutoff replacement value,divisor)
  | L.Max (a,b) -> L.Max (substitute_expression remove cutoff replacement a,substitute_expression remove cutoff replacement b)
  | L.Min (a,b) -> L.Min (substitute_expression remove cutoff replacement a,substitute_expression remove cutoff replacement b)
let rec substitute_test remove cutoff replacement = function
  | L.LE (a,b) -> L.LE (substitute_expression remove cutoff replacement a,substitute_expression remove cutoff replacement b)
  | L.EQ (a,b) -> L.EQ (substitute_expression remove cutoff replacement a,substitute_expression remove cutoff replacement b)
  | L.And (a,b) -> L.And (substitute_test remove cutoff replacement a,substitute_test remove cutoff replacement b)
  | L.Or (a,b) -> L.Or (substitute_test remove cutoff replacement a,substitute_test remove cutoff replacement b)
  | L.Not value -> L.Not (substitute_test remove cutoff replacement value)
  | L.TConstantTest _ as value -> value
let rec substitute_statement remove cutoff replacement = function
  | L.Loop (lower,upper,body) -> L.Loop (substitute_expression remove cutoff replacement lower,
      substitute_expression remove cutoff replacement upper,substitute_statement remove (cutoff+1) replacement body)
  | L.Guard (test,body) -> L.Guard (substitute_test remove cutoff replacement test,substitute_statement remove cutoff replacement body)
  | L.Instr (instruction,args) -> L.Instr (instruction,List.map (substitute_expression remove cutoff replacement) args)
  | L.Seq sequence -> L.Seq (substitute_sequence remove cutoff replacement sequence)
and substitute_sequence remove cutoff replacement = function
  | L.SNil -> L.SNil
  | L.SCons (head,tail) -> L.SCons (substitute_statement remove cutoff replacement head,substitute_sequence remove cutoff replacement tail)

let is_singleton lower upper = match linear (subtract upper lower) with
  | Some (coefficients, constant) -> Coefficients.is_empty coefficients && Z.equal constant Z.one
  | None -> false
let singleton_eliminate code =
  let count = ref 0 in
  let rec clean = function
    | L.Loop (lower,upper,body) ->
        let body = clean body in
        if is_singleton lower upper then (incr count; substitute_statement true 0 lower body)
        else L.Loop (lower,upper,body)
    | L.Guard (test,body) -> L.Guard (test,clean body)
    | L.Seq sequence -> L.Seq (clean_sequence sequence)
    | code -> code
  and clean_sequence = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (clean head,clean_sequence tail) in
  let result = clean code in result, !count

(* This first recovery handles the innermost point coordinate only. A unit
   coefficient allows translating its binder by the remaining affine offset.
   All eligible arguments in that body must agree; nested loops defer recovery. *)
let point_offset code =
  let offsets = ref [] in
  let rec collect = function
    | L.Loop _ -> raise Exit
    | L.Guard (_,body) -> collect body
    | L.Seq sequence -> collect_sequence sequence
    | L.Instr (_,args) -> List.iter (fun arg -> match linear arg with
        | Some (coefficients, constant) when
            Coefficients.find_opt 0 coefficients = Some Z.one ->
              offsets := (Coefficients.remove 0 coefficients,constant) :: !offsets
        | _ -> ()) args
  and collect_sequence = function
    | L.SNil -> ()
    | L.SCons (head,tail) -> collect head; collect_sequence tail in
  try
    collect code;
    match !offsets with
    | [] -> None
    | offset::rest when List.for_all (form_equal offset) rest ->
        let coefficients,constant = offset in
        if Coefficients.is_empty coefficients && Z.equal constant Z.zero then None
        else Some (expression (Coefficients.fold (fun index value result ->
          Coefficients.add (index-1) value result) coefficients Coefficients.empty,constant))
    | _ -> None
  with Exit -> None

let rec shift_bound offset = function
  | L.Max (a,b) -> L.Max (shift_bound offset a,shift_bound offset b)
  | L.Min (a,b) -> L.Min (shift_bound offset a,shift_bound offset b)
  | L.Div (value,divisor) -> L.Div (add value (L.Mult (divisor,offset)),divisor)
  | value -> add value offset
let recover_points code =
  let count = ref 0 in
  let rec recover = function
    | L.Loop (lower,upper,body) ->
        let body = recover body in
        (match point_offset body with
         | None -> L.Loop (lower,upper,body)
         | Some offset ->
             incr count;
             let old_coordinate = subtract (L.Var (nat 0)) (lift_by 1 offset) in
             L.Loop (shift_bound offset lower,shift_bound offset upper,
               substitute_statement false 0 old_coordinate body))
    | L.Guard (test,body) -> L.Guard (test,recover body)
    | L.Seq sequence -> L.Seq (recover_sequence sequence)
    | code -> code
  and recover_sequence = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (recover head,recover_sequence tail) in
  let result = recover code in result, !count

let adapt limit ((raw,context),variables) =
  incr adaptations;
  try
    let path = match !current_path with Some path -> path | None -> failwith "missing tiling phase receipt" in
    emit (Filename.concat path "raw-generated.loop") (statement "" raw);
    let enabled = Sys.getenv_opt "GUARDCERT_POINT_NORMALIZATION" <> Some "disabled" in
    let without_singletons, singletons = if enabled then singleton_eliminate raw else raw,0 in
    let recovered, translations = if enabled then recover_points without_singletons else without_singletons,0 in
    emit (Filename.concat path "point-normalized.loop") (statement "" recovered);
    emit (Filename.concat path "point-normalization.txt")
      (Printf.sprintf "enabled=%b singleton_loops_removed=%d point_translations=%d\n" enabled singletons translations);
    let unit_links = List.exists (fun witness -> List.exists (fun link ->
      Z.equal (GuardMemoryNumbers.export_integer link.TilingWitness.tl_tile_size) Z.one)
      witness.TilingWitness.stw_links) !current_witnesses in
    let completed = if unit_links then (
      if not (List.for_all canonical !current_witnesses) then
        invalid_arg "affine unit coordinates require a new completion proposal";
      Coordinates.complete_unit_points (Coordinates.unit_axes !current_witnesses) recovered
    ) else recovered in
    emit (Filename.concat path "completed.loop") (statement "" completed);
    emit (Filename.concat path "coordinate-completion.txt") ("unit-links=" ^ string_of_bool unit_links ^ "\n");
    emit (Filename.concat path "adaptation-limit.txt") (integer_text limit ^ "\n");
    let generated = adapt_at 0 completed in
    let generated = if Sys.getenv_opt "GUARDCERT_POINT_NORMALIZATION" = Some "wrong-coordinate" then
      let rec damage = function
        | L.Instr (instruction,first::rest) -> L.Instr (instruction,add first one::rest)
        | L.Loop (a,b,body) -> L.Loop (a,b,damage body)
        | L.Guard (test,body) -> L.Guard (test,damage body)
        | L.Seq sequence -> L.Seq (damage_sequence sequence)
        | code -> code
      and damage_sequence = function
        | L.SNil -> L.SNil
        | L.SCons (head,tail) -> L.SCons (damage head,damage_sequence tail) in
      damage generated else generated in
    emit (Filename.concat path "generated.loop") (statement "" generated);
    emit (Filename.concat path "adaptation.txt")
      "raw-phase-checks=accepted\nprepared-codegen=successful\npoint-normalization=proposed\nbound-adaptation=proposed\nfinal-candidate-check=pending\n";
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
    (match !current_path with Some path -> emit (Filename.concat path "adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None -> ());
    Result.Err (Printexc.to_string error)
