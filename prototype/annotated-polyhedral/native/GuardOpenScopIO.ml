(* Untrusted OpenScop transport. The verified importer and validators consume
   its results; instruction bodies are never imported into the execution model. *)
open OpenScop
let rec nat_to_int = function Datatypes.O -> 0 | Datatypes.S n -> 1 + nat_to_int n
let rec nat n = if n < 0 || n > 100000 then invalid_arg "OpenScop size" else
  if n = 0 then Datatypes.O else Datatypes.S (nat (n-1))
let integer = GuardMemoryNumbers.export_integer
let integer_text x = Z.to_string (integer x)
let bin symbol left right = "(" ^ left ^ " " ^ symbol ^ " " ^ right ^ ")"
(* PolCert's expanded affine substitutions contain many zero products. Keep
   the untrusted textual body compact enough for the OSL body reader. Relation
   matrices, rather than this presentation, determine checked import. *)
let affine_bin symbol left right = match symbol,left,right with
  | "+","0",e | "+",e,"0" | "-",e,"0" -> e
  | "*","0",_ | "*",_,"0" -> "0"
  | "*","1",e | "*",e,"1" -> e
  | _ -> bin symbol left right
let rec affine = function
  | AfInt n -> integer_text n | AfVar name -> name
  | AfAdd (a,b) -> affine_bin "+" (affine a) (affine b)
  | AfMinus (a,b) -> affine_bin "-" (affine a) (affine b)
  | AfMulti (a,b) -> affine_bin "*" (affine a) (affine b)
  | AfDiv (a,b) -> bin "/" (affine a) (affine b)
let access (ArrAccess (name,coordinates)) = name ^ String.concat "" (List.map (fun e -> "[" ^ affine e ^ "]") coordinates)
let rec expression = function
  | ArrAtom (AInt n) -> integer_text n | ArrAtom (AVar name) -> name
  | ArrAccessAtom a -> access a
  | ArrAdd (a,b) -> bin "+" (expression a) (expression b)
  | ArrMinus (a,b) -> bin "-" (expression a) (expression b)
  | ArrMulti (a,b) -> bin "*" (expression a) (expression b)
  | ArrDiv (a,b) -> bin "/" (expression a) (expression b)
  | _ -> invalid_arg "unsupported OpenScop body"
let body = function ArrAssign (a,e) -> access a ^ " = " ^ expression e ^ ";" | ArrSkip -> ";"
let relation ?(array_ids=[]) channel r =
  let kind = match r.rel_type with CtxtTy -> "CONTEXT" | DomTy -> "DOMAIN" | ScttTy -> "SCATTERING"
    | ReadTy -> "READ" | WriteTy -> "WRITE" | MayWriteTy -> "MAYWRITE" in
  Printf.fprintf channel "%s\n" kind;
  let m = r.meta in
  Printf.fprintf channel "%d %d %d %d %d %d\n" (nat_to_int m.row_nb) (nat_to_int m.col_nb)
    (nat_to_int m.out_dim_nb) (nat_to_int m.in_dim_nb) (nat_to_int m.local_dim_nb) (nat_to_int m.param_nb);
  List.iteri (fun index (inequality,row) ->
    if List.length row+1 <> nat_to_int m.col_nb then invalid_arg "exported OpenScop row width";
    let row = match r.rel_type,index,List.rev row with
      | (ReadTy | WriteTy | MayWriteTy),0,identifier::tail ->
        let dense = List.assoc (integer_text identifier) array_ids in
        List.rev (GuardMemoryNumbers.import_integer (Z.of_int dense)::tail)
      | _ -> row in
    Printf.fprintf channel "%d %s\n" (if inequality then 1 else 0)
    (String.concat " " (List.map integer_text row))) r.constrs
let write path scop =
  (* Pluto indexes the <arrays> names by id-1. CompCert positives are sparse,
     so transport uses dense IDs; the verified importer retains source access
     functions and never trusts the returned array table or instructions. *)
  let arrays = List.concat_map (function ArrayExt a -> a | _ -> []) scop.glb_exts in
  let array_ids = List.mapi (fun index (id,_) ->
    Z.to_string (GuardMemoryNumbers.export_positive id),index+1) arrays in
  let channel = open_out path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () ->
    output_string channel "<OpenScop>\nC\n";
    relation channel scop.context.param_domain;
    (match scop.context.params with None | Some [] -> output_string channel "0\n"
      | Some names -> Printf.fprintf channel "1\n<strings>\n%s\n</strings>\n" (String.concat " " names));
    Printf.fprintf channel "%d\n" (List.length scop.statements);
    List.iter (fun statement ->
      Printf.fprintf channel "%d\n" (2+List.length statement.access);
      List.iter (relation ~array_ids channel) (statement.domain :: statement.scattering :: statement.access);
      let extensions = Option.value statement.stmt_exts_opt ~default:[] in
      Printf.fprintf channel "%d\n" (List.length extensions);
      List.iter (fun (StmtBody (iterators,statement)) ->
        let text = body statement in
        if String.length text > 2048 then invalid_arg "OpenScop body too long";
        Printf.fprintf channel "<body>\n%d\n%s\n%s\n</body>\n"
          (List.length iterators) (String.concat " " iterators) text) extensions)
      scop.statements;
    Printf.fprintf channel "<arrays>\n%d\n" (List.length arrays);
    List.iteri (fun index (_,name) -> Printf.fprintf channel "%d %s\n" (index+1) name) arrays;
    output_string channel "</arrays>\n";
    output_string channel "</OpenScop>\n")
let words line = String.split_on_char ' ' (String.map (function '\t' -> ' ' | c -> c) line)
  |> List.filter (fun s -> s <> "")
let read source path =
  let channel = open_in path in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
    let rec next () =
      let raw = input_line channel in
      let line = String.trim (List.hd (String.split_on_char '#' raw)) in
      if line = "" then next () else line in
    let expect wanted = if next () <> wanted then invalid_arg ("expected " ^ wanted) in
    let size () = let n = int_of_string (next ()) in ignore (nat n); n in
    let rec find_start () = if next () <> "<OpenScop>" then find_start () in
    let read_relation () =
      let kind = match next () with "CONTEXT" -> CtxtTy | "DOMAIN" -> DomTy | "SCATTERING" -> ScttTy
        | "READ" -> ReadTy | "WRITE" -> WriteTy | "MAYWRITE" -> MayWriteTy | _ -> invalid_arg "relation kind" in
      let metadata = List.map int_of_string (words (next ())) in
      let m = match metadata with [rows;cols;outputs;inputs;locals;parameters] ->
        { row_nb=nat rows; col_nb=nat cols; out_dim_nb=nat outputs; in_dim_nb=nat inputs;
          local_dim_nb=nat locals; param_nb=nat parameters }
        | _ -> invalid_arg "relation metadata" in
      let rows = List.init (nat_to_int m.row_nb) (fun _ ->
        match words (next ()) with flag::row when List.length row+1=nat_to_int m.col_nb ->
          if flag <> "0" && flag <> "1" then invalid_arg "relation equality flag";
          flag="1",List.map (fun s -> GuardMemoryNumbers.import_integer (Z.of_string s)) row
        | _ -> invalid_arg "relation row width") in
      { rel_type=kind; meta=m; constrs=rows } in
    find_start (); expect "C";
    let context = read_relation () in
    if context.rel_type <> CtxtTy then invalid_arg "context relation";
    (match size () with 0 -> () | 1 -> expect "<strings>";
      let rec names () = if next () <> "</strings>" then names () in names ()
      | _ -> invalid_arg "parameter name flag");
    let count = size () in
    if count <> List.length source.statements then invalid_arg "statement count changed";
    let statements = List.init count (fun index ->
      let relations = List.init (size ()) (fun _ -> read_relation ()) in
      let extensions = size () in
      for _ = 1 to extensions do
        let tag = next () in
        if String.length tag < 3 || tag.[0] <> '<' then invalid_arg "extension tag";
        let finish = "</" ^ String.sub tag 1 (String.length tag-1) in
        let rec skip () = if next () <> finish then skip () in skip ()
      done;
      let original = List.nth source.statements index in
      { domain=List.find (fun r -> r.rel_type=DomTy) relations;
        scattering=List.find (fun r -> r.rel_type=ScttTy) relations;
        access=List.filter (fun r -> r.rel_type=ReadTy || r.rel_type=WriteTy || r.rel_type=MayWriteTy) relations;
        stmt_exts_opt=original.stmt_exts_opt }) in
    { context={ source.context with param_domain=context }; statements; glb_exts=source.glb_exts })
