(* An untrusted candidate names existing instruction sites; the extracted
   checker establishes domain, argument, instruction and dependence agreement. *)
module L = GuardMemoryPolyhedral.GuardMemoryIRs.Loop
type sexpr = Atom of string | List of sexpr list

let input_limit = 1048576
let node_limit = 50000
let depth_limit = 128

let read_input channel =
  let buffer = Buffer.create 4096 in
  (try while true do
     let line = input_line channel in
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

let rec loop_expression = function
  | List [Atom "constant"; value] -> L.Constant (GuardMemoryNumbers.import_integer (integer value))
  | List [Atom "var"; index] -> L.Var (natural (small index))
  | List [Atom "sum"; first; second] -> L.Sum (loop_expression first, loop_expression second)
  | List [Atom "scale"; coefficient; value] -> L.Mult (GuardMemoryNumbers.import_integer (integer coefficient), loop_expression value)
  | List [Atom "div"; value; divisor] -> L.Div (loop_expression value, GuardMemoryNumbers.import_integer (integer divisor))
  | List [Atom "mod"; value; divisor] -> L.Mod (loop_expression value, GuardMemoryNumbers.import_integer (integer divisor))
  | List [Atom "min"; first; second] -> L.Min (loop_expression first, loop_expression second)
  | List [Atom "max"; first; second] -> L.Max (loop_expression first, loop_expression second)
  | _ -> invalid_arg "Loop expression"
let rec loop_test = function
  | List [Atom "le"; first; second] -> L.LE (loop_expression first, loop_expression second)
  | List [Atom "eq"; first; second] -> L.EQ (loop_expression first, loop_expression second)
  | List [Atom "and"; first; second] -> L.And (loop_test first, loop_test second)
  | List [Atom "or"; first; second] -> L.Or (loop_test first, loop_test second)
  | List [Atom "not"; test] -> L.Not (loop_test test)
  | _ -> invalid_arg "Loop test"

let rec instantiate_at instructions current = function
  | List [Atom "loop"; lower; upper; body] ->
    L.Loop (loop_expression lower,loop_expression upper,instantiate_at instructions current body)
  | List (Atom "seq" :: statements) ->
    if List.length statements > 32 then invalid_arg "candidate statement-list limit";
    L.Seq (List.fold_right (fun statement rest -> L.SCons (instantiate_at instructions current statement,rest)) statements L.SNil)
  | List [Atom "guard"; test; body] -> L.Guard (loop_test test,instantiate_at instructions current body)
  | List [Atom "each"; body] ->
    if List.length instructions > 32 then invalid_arg "candidate site-list limit";
    let statements = List.mapi (fun site _ -> instantiate_at instructions (Some site) body) instructions in
    L.Seq (List.fold_right (fun statement rest -> L.SCons (statement,rest)) statements L.SNil)
  | List [Atom "instr"; site; List arguments] ->
    let site = match site,current with
      | Atom "current",Some site -> site | _ -> small site in
    let instruction = match List.nth_opt instructions site with
      | Some instruction -> instruction | None -> invalid_arg "candidate instruction site" in
    L.Instr (instruction,List.map loop_expression arguments)
  | _ -> invalid_arg "candidate statement"

let template = lazy (match Sys.getenv_opt "GUARDCERT_LOOP_CANDIDATE" with
  | None -> None
  | Some path ->
    let channel = open_in path in
    Fun.protect ~finally:(fun () -> close_in channel)
      (fun () -> Some (parse (read_input channel))))

let propose instructions =
  try match Lazy.force template with
    | Some (List [Atom "reindex"; List swaps; syntax]) ->
      Some (instantiate_at instructions None syntax,List.map (fun slot -> natural (small slot)) swaps)
    | Some syntax -> Some (instantiate_at instructions None syntax,[])
    | None -> None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
