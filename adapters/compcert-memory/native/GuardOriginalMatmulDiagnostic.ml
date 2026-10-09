(* Read-only diagnostic on the actual normalized input reaching the printer. *)
let rec difference path first second =
  if first = second then None
  else if Obj.is_int first || Obj.is_int second then
    Some (Printf.sprintf "%s immediate expected=%s actual=%s" path
      (if Obj.is_int first then string_of_int (Obj.obj first : int) else "block")
      (if Obj.is_int second then string_of_int (Obj.obj second : int) else "block"))
  else if Obj.tag first <> Obj.tag second || Obj.size first <> Obj.size second then
    Some (Printf.sprintf "%s tag/size expected=%d/%d actual=%d/%d" path
      (Obj.tag first) (Obj.size first) (Obj.tag second) (Obj.size second))
  else if Obj.tag first >= Obj.no_scan_tag then Some (path ^ " opaque numeric value differs")
  else let rec fields index =
    if index = Obj.size first then None else
    match difference (path ^ "." ^ string_of_int index) (Obj.field first index) (Obj.field second index) with
    | Some reason -> Some reason | None -> fields (index+1) in fields 0
let rec inspect = function
  | Clight.Slabel (label,body) ->
    if List.mem label (GuardScopFrontend.chosen_labels ()) then begin
      let exact = body = OriginalMatmulBody.original_matmul_region in
      let mismatch = difference "root" (Obj.repr OriginalMatmulBody.original_matmul_region) (Obj.repr body) in
      Printf.eprintf "GUARDCERT_ORIGINAL_SOURCE exact=%b mismatch=%S\n%!" exact (Option.value mismatch ~default:"none")
    end;
    inspect body
  | Clight.Ssequence (first,second) | Clight.Sloop (first,second) -> inspect first; inspect second
  | Clight.Sifthenelse (_,yes,no) -> inspect yes; inspect no
  | Clight.Sswitch (_,cases) -> inspect_cases cases
  | _ -> ()
and inspect_cases = function
  | Clight.LSnil -> () | Clight.LScons (_,body,rest) -> inspect body; inspect_cases rest
let print program =
  List.iter (fun (_,definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) -> inspect fn.Clight.fn_body
    | _ -> ()) program.Ctypes.prog_defs;
  GuardOriginalMatmulCandidate.trace_clight program;
  PrintClight.print_if program
