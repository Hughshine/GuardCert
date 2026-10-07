(* Capture explicit region selection before CompCert discards local pragmas.
   The generated labels are control metadata, not assumptions. Semantic and
   placement checks still run on the actual normalized source statements. *)
open Cabs
module Names = Set.Make(String)

type selection = {
  label : string;
  opening : loc;
  closing : loc;
  statements : int;
}
type refusal = { function_location : loc; reason : string }
type manifest = { regions : selection list; refused : refusal list }
let latest = ref { regions = []; refused = [] }

exception Refused of string

let marker = function
  | DEFINITION (PRAGMA (text, location)) ->
      (match String.trim text with
       | "scop" -> Some (`Open, location)
       | "endscop" -> Some (`Close, location)
       | _ -> None)
  | _ -> None

let children = function
  | BLOCK (body,_) -> body
  | If (_,yes,no,_) -> yes :: (match no with Some no -> [no] | None -> [])
  | WHILE (_,body,_) | DOWHILE (_,body,_) | FOR (_,_,_,body,_)
  | SWITCH (_,body,_) | CASE (_,body,_) | DEFAULT (body,_)
  | LABEL (_,body,_) -> [body]
  | _ -> []

let rec mentioned_names names statement =
  let names = match statement with
    | LABEL (name,_,_) | GOTO (name,_) -> Names.add name names
    | _ -> names in
  List.fold_left mentioned_names names (children statement)

let names_in_program program = List.fold_left (fun names -> function
  | FUNDEF (_,_,_,body,_) -> mentioned_names names body
  | _ -> names) Names.empty program

let program input =
  latest := { regions = []; refused = [] };
  let used = ref (names_in_program input) in
  let next = ref 0 in
  let rec fresh () =
    incr next;
    let name = "__guardcert_scop_" ^ string_of_int !next in
    if Names.mem name !used then fresh ()
    else (used := Names.add name !used; name) in
  let regions = ref [] and refused = ref [] in
  let transform_function spec name definitions body location =
    let selected = ref [] in
    let rec statement inside = function
      | BLOCK (body,location) -> BLOCK (statements inside body,location)
      | If (condition,yes,no,location) ->
          If (condition,statement inside yes,Option.map (statement inside) no,location)
      | WHILE (condition,body,location) -> WHILE (condition,statement inside body,location)
      | DOWHILE (condition,body,location) -> DOWHILE (condition,statement inside body,location)
      | FOR (initial,test,increment,body,location) ->
          FOR (initial,test,increment,statement inside body,location)
      | SWITCH (condition,body,location) -> SWITCH (condition,statement inside body,location)
      | CASE (condition,body,location) -> CASE (condition,statement inside body,location)
      | DEFAULT (body,location) -> DEFAULT (statement inside body,location)
      | LABEL (name,body,location) -> LABEL (name,statement inside body,location)
      | other -> (match marker other with
          | None -> other
          | Some _ -> raise (Refused "region markers must be paired within one block"))
    and statements inside body = match body with
      | [] -> []
      | head :: rest ->
          (match marker head with
           | None -> statement inside head :: statements inside rest
           | Some (`Close,_) -> raise (Refused "unmatched endscop")
           | Some (`Open,opening) ->
               if inside then raise (Refused "nested region markers are unsupported");
               let rec collect reversed = function
                 | [] -> raise (Refused "unmatched scop")
                 | candidate :: tail ->
                     (match marker candidate with
                      | Some (`Open,_) -> raise (Refused "nested region markers are unsupported")
                      | Some (`Close,closing) -> List.rev reversed,closing,tail
                      | None -> collect (candidate :: reversed) tail) in
               let selected_body,closing,tail = collect [] rest in
               if selected_body = [] then raise (Refused "empty region");
               (* Adding a surrounding block must not shorten declaration
                  scope. Declarations inside existing nested blocks keep their
                  original scope; declarations directly in this span refuse. *)
               if List.exists (function DEFINITION _ -> true | _ -> false) selected_body
               then raise (Refused "declarations at region scope require a different boundary encoding");
               let label = fresh () in
               let body = List.map (statement true) selected_body in
               selected := { label; opening; closing;
                 statements = List.length selected_body } :: !selected;
               LABEL (label,BLOCK (body,opening),opening) :: statements inside tail) in
    try
      let body = statement false body in
      regions := !selected @ !regions;
      FUNDEF (spec,name,definitions,body,location)
    with Refused reason ->
      refused := { function_location = location; reason } :: !refused;
      (* CompCert's usual elaborator ignores the original local pragmas. Keep
         the whole function exactly as supplied when selection is unsupported. *)
      FUNDEF (spec,name,definitions,body,location) in
  let result = List.map (function
    | FUNDEF (spec,name,definitions,body,location) ->
        transform_function spec name definitions body location
    | other -> other) input in
  latest := { regions = List.rev !regions; refused = List.rev !refused };
  result

let chosen_labels () =
  List.map (fun region -> Camlcoq.intern_string region.label) (!latest).regions

let trace () = if Sys.getenv_opt "GUARDCERT_SCOP_DIAGNOSTICS" = Some "1" then begin
  List.iter (fun region -> Printf.eprintf
    "GUARDCERT_SCOP label=%s file=%S begin=%d end=%d statements=%d\n%!"
    region.label region.opening.filename region.opening.lineno
    region.closing.lineno region.statements) (!latest).regions;
  List.iter (fun refusal -> Printf.eprintf
    "GUARDCERT_SCOP_REFUSED file=%S line=%d reason=%S\n%!"
    refusal.function_location.filename refusal.function_location.lineno
    refusal.reason) (!latest).refused
end
