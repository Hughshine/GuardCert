(* This reader proposes data to the extracted checker. It does not establish
   the connection from a C program to this IR; that is the language bridge. *)
module IR = GuardMemoryPolyhedral.GuardMemoryIRs.PolyLang

type sexpr = Atom of string | List of sexpr list

let input_limit = 1048576
let node_limit = 50000
let depth_limit = 128

let read_input () =
  let buffer = Buffer.create 4096 in
  (try while true do
     let line = input_line stdin in
     if Buffer.length buffer + String.length line > input_limit then invalid_arg "input limit";
     Buffer.add_string buffer line; Buffer.add_char buffer '\n'
   done with End_of_file -> ());
  Buffer.contents buffer

let parse raw =
  let position = ref 0 and nodes = ref 0 in
  let whitespace = function ' ' | '\n' | '\r' | '\t' -> true | _ -> false in
  let rec skip () =
    while !position < String.length raw && whitespace raw.[!position] do incr position done in
  let rec expression depth =
    incr nodes;
    if !nodes > node_limit || depth > depth_limit then invalid_arg "parser limit";
    skip ();
    if !position >= String.length raw then invalid_arg "unexpected end";
    match raw.[!position] with
    | ')' -> invalid_arg "unexpected closing parenthesis"
    | '(' ->
      incr position;
      let rec members result =
        skip ();
        if !position >= String.length raw then invalid_arg "unclosed list";
        if raw.[!position] = ')' then (incr position; List (List.rev result))
        else members (expression (depth + 1) :: result) in
      members []
    | _ ->
      let start = !position in
      while !position < String.length raw && not (whitespace raw.[!position])
          && raw.[!position] <> '(' && raw.[!position] <> ')' do incr position done;
      Atom (String.sub raw start (!position - start)) in
  let result = expression 0 in
  skip ();
  if !position <> String.length raw then invalid_arg "trailing input";
  result

let atom = function Atom text -> text | _ -> invalid_arg "expected atom"
let members = function List elements -> elements | _ -> invalid_arg "expected list"
let integer value =
  let text = atom value in
  if String.length text > 128 then invalid_arg "integer limit";
  Z.of_string text
let small value =
  let value = integer value in
  if Z.sign value < 0 || Z.compare value (Z.of_int 256) > 0 then invalid_arg "natural limit";
  Z.to_int value
let rec natural = function 0 -> Datatypes.O | n -> Datatypes.S (natural (n - 1))
let positive value =
  let value = integer value in
  if Z.sign value <= 0 then invalid_arg "identifier must be positive";
  value

let field name fields =
  let selected = List.filter_map (function
    | List (Atom key :: values) when key = name -> Some values | _ -> None) fields in
  match selected with [values] -> values | _ -> invalid_arg ("missing or duplicate " ^ name)
let one = function [value] -> value | _ -> invalid_arg "expected one value"
let rows expressions = List.map (fun expression ->
  match List.rev (members expression) with
  | bias :: coefficients -> (List.map integer (List.rev coefficients), integer bias)
  | [] -> invalid_arg "empty affine row") expressions
let access expression =
  match members expression with
  | identifier :: coordinates -> (positive identifier, rows coordinates)
  | [] -> invalid_arg "empty access"

let rec value_expression = function
  | List [Atom "constant"; value] -> GuardMemoryRuntime.ConstantValue (integer value)
  | List [Atom "parameter"; value] -> GuardMemoryRuntime.ParameterValue (natural (small value))
  | List [Atom "loaded"; value] -> GuardMemoryRuntime.LoadedValue (natural (small value))
  | List [Atom "add"; first; second] -> GuardMemoryRuntime.AddValue (value_expression first, value_expression second)
  | List [Atom "sub"; first; second] -> GuardMemoryRuntime.SubValue (value_expression first, value_expression second)
  | List [Atom "mul"; first; second] -> GuardMemoryRuntime.MulValue (value_expression first, value_expression second)
  | _ -> invalid_arg "value expression"

let witness = function
  | List [Atom "identity"; dimension] -> PointWitness.PSWIdentity (natural (small dimension))
  | List [Atom "tiling"; dimension; List links] ->
    let links = List.map (function
      | List [List coefficients; List parameters; bias; width] -> {
        TilingWitness.tl_expr = {
          TilingWitness.ae_var_coeffs = List.map integer coefficients;
          ae_param_coeffs = List.map integer parameters;
          ae_const = integer bias };
        tl_tile_size = integer width }
      | _ -> invalid_arg "tile link") links in
    PointWitness.PSWTiling { TilingWitness.stw_point_dim = natural (small dimension);
                            stw_links = links }
  | _ -> invalid_arg "point witness"

let statement expression =
  let fields = members expression in
  let write = access (one (field "write" fields)) in
  let reads = List.map access (field "reads" fields) in
  let instruction = {
    GuardMemoryInstr.instruction_write = write;
    instruction_reads = reads;
    instruction_value = value_expression (one (field "value" fields)) } in
  { IR.pi_depth = natural (small (one (field "depth" fields)));
    pi_instr = instruction;
    pi_poly = rows (field "domain" fields);
    pi_schedule = rows (field "schedule" fields);
    pi_point_witness = witness (one (field "witness" fields));
    pi_transformation = rows (field "transformation" fields);
    pi_access_transformation = rows (field "access-transformation" fields);
    pi_waccess = List.map access (field "waccess" fields);
    pi_raccess = List.map access (field "raccess" fields) }

let program expression =
  let fields = members expression in
  let context = List.map positive (field "context" fields) in
  let variables = List.map (fun identifier -> (positive identifier, ())) (field "variables" fields) in
  let statements = field "statements" fields in
  if List.length statements > 32 then invalid_arg "statement limit";
  ((List.map statement statements, context), variables)

let run () =
  let mode, source, candidate, witnesses = match parse (read_input ()) with
    | List [Atom "affine"; source; candidate] -> "affine", program source, program candidate, []
    | List [Atom "tiling"; source; candidate; List witnesses] ->
      let witnesses = List.map (fun expression -> match witness expression with
        | PointWitness.PSWTiling w -> w | _ -> invalid_arg "tiling witness expected") witnesses in
      "tiling", program source, program candidate, witnesses
    | _ -> invalid_arg "expected mode, source, candidate, and witnesses for tiling" in
  let result = match mode with
    | "affine" -> GuardMemoryPolyhedral.validate_memory_equivalence source candidate
    | "tiling" -> GuardMemoryPolyhedral.GuardMemoryTilingValidator.checked_tiling_validate_poly source candidate witnesses
    | _ -> invalid_arg "mode must be affine or tiling" in
  let observed = ref None in
  let _ = ImpureConfig.Core.Base.bind result (fun pair ->
    observed := Some pair; ImpureConfig.Core.Base.pure ()) in
  let accepted, alarm_free = match !observed with
    | Some pair -> pair | None -> failwith "extracted pure monad did not return" in
  Printf.printf "{\"accepted\":%b,\"alarm_free\":%b,\"mode\":\"%s\",\"oracle_searches\":%d,\"oracle_contradictions\":%d,\"oracle_exhausted\":%d}\n"
    (accepted && alarm_free) alarm_free mode
    !GuardMemoryOracle.searches !GuardMemoryOracle.contradictions !GuardMemoryOracle.exhausted

let () =
  try run () with
  | Invalid_argument message | Failure message ->
    Printf.eprintf "invalid validator input: %s\n" message; exit 2
  | Stack_overflow -> Printf.eprintf "validator stack limit\n"; exit 2
