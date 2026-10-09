(* Execute the extracted capture AST with extracted Cop operations and Mem loads.
   This probe supplies global block lookup; it does not run the original source
   or constitute a C-to-Asm compiler or a proved Clight interpreter. *)
module C = Clight
module M = Memory.Mem
module I = Integers.Int
module L = Integers.Int64

let emit path content =
  let out = open_out path in
  Fun.protect ~finally:(fun () -> close_out out) (fun () -> output_string out content)
let checked = function Some value -> value | None -> failwith "undefined extracted machine operation"
let rec statement = function
  | C.Sskip -> "skip"
  | C.Sset (id,e) -> "set " ^ Z.to_string id ^ " " ^ expression e
  | C.Ssequence (a,b) -> "seq(" ^ statement a ^ "," ^ statement b ^ ")"
  | C.Sifthenelse (e,a,b) -> "if(" ^ expression e ^ "," ^ statement a ^ "," ^ statement b ^ ")"
  | _ -> failwith "unexpected capture statement"
and expression = function
  | C.Econst_int (n,_) -> "int " ^ Z.to_string (I.signed n)
  | C.Econst_long (n,_) -> "long " ^ Z.to_string (L.signed n)
  | C.Evar (id,_) -> "global " ^ Z.to_string id
  | C.Etempvar (id,_) -> "temp " ^ Z.to_string id
  | C.Ebinop (Cop.Olt,a,b,_) -> "lt(" ^ expression a ^ "," ^ expression b ^ ")"
  | C.Ecast (a,_) -> "cast(" ^ expression a ^ ")"
  | _ -> failwith "unexpected capture expression"

let () =
  if Array.length Sys.argv <> 5 then invalid_arg "probe M_OR_UNDEF N_OR_UNDEF K_OR_UNDEF NEW_OUTPUT_DIRECTORY";
  let output = Sys.argv.(4) in
  Unix.mkdir output 0o700;
  let identifiers = [OriginalMatmul._M;OriginalMatmul._N;OriginalMatmul._K] in
  let headers = List.map (fun x -> if x = "undef" then None else Some (Z.of_string x))
    [Sys.argv.(1);Sys.argv.(2);Sys.argv.(3)] in
  let memory,blocks = List.fold_left2 (fun (memory,blocks) id value ->
    let memory,block = M.alloc memory Z.zero (Z.of_int 8) in
    let memory = match value with None -> memory | Some value ->
      checked (M.store AST.Mint64 memory block Z.zero (Values.Vlong (L.repr value))) in
    memory,blocks@[id,block]) (M.empty,[]) identifiers headers in
  let reads = Hashtbl.create 3 and temps = Hashtbl.create 10 in
  List.iter (fun id -> Hashtbl.add reads id 0) identifiers;
  let public = [OriginalMatmul._i,37;OriginalMatmul._j,41;OriginalMatmul._k__1,43] in
  List.iter (fun (id,value) -> Hashtbl.add temps id (Values.Vlong (L.repr (Z.of_int value)))) public;
  let rec evaluate = function
    | C.Econst_int (n,_) -> Values.Vint n
    | C.Econst_long (n,_) -> Values.Vlong n
    | C.Etempvar (id,_) -> (match Hashtbl.find_opt temps id with Some value -> value | None -> Values.Vundef)
    | C.Evar (id,_) ->
        Hashtbl.replace reads id (1+Hashtbl.find reads id);
        checked (M.load AST.Mint64 memory (List.assoc id blocks) Z.zero)
    | C.Ebinop (Cop.Olt,a,b,_) ->
        let first = evaluate a in
        let second = evaluate b in
        checked (Cop.sem_cmp Integers.Clt first (C.typeof a) second (C.typeof b) memory)
    | C.Ecast (a,ty) -> checked (Cop.sem_cast (evaluate a) (C.typeof a) ty memory)
    | _ -> failwith "unexpected executed expression" in
  let rec run = function
    | C.Sskip -> ()
    | C.Sset (id,e) -> Hashtbl.replace temps id (evaluate e)
    | C.Ssequence (a,b) -> run a; run b
    | C.Sifthenelse (e,a,b) -> run (if checked (Cop.bool_val (evaluate e) (C.typeof e) memory) then a else b)
    | _ -> failwith "unexpected executed statement" in
  let code = OriginalMatmulCapture.original_matmul_capture_code in
  emit (Filename.concat output "capture.statement") (statement code ^ "\n");
  run code;
  let slots = OriginalMatmulCapture.original_matmul_captures in
  let flag = match Hashtbl.find temps slots.GuardMemoryDoubleMatmulCapture.matmul_capture_flag with
    | Values.Vint word -> Z.equal (I.signed word) Z.one | _ -> failwith "undefined capture flag" in
  let cache id = match Hashtbl.find_opt temps id with
    | Some (Values.Vint word) -> Z.to_string (I.signed word) | _ -> "null" in
  let caches = [slots.GuardMemoryDoubleMatmulCapture.matmul_capture_M;
    slots.GuardMemoryDoubleMatmulCapture.matmul_capture_N;slots.GuardMemoryDoubleMatmulCapture.matmul_capture_K] in
  let unchanged = List.for_all (fun (id,value) ->
    match Hashtbl.find temps id with Values.Vlong word -> Z.equal (L.signed word) (Z.of_int value) | _ -> false) public in
  if not unchanged then failwith "public iterator changed";
  emit (Filename.concat output "result.json") (Printf.sprintf
    "{\"accepted\":%b,\"captured\":[%s],\"header_reads\":[%s],\"public_iterators_unchanged\":true,\"source_or_candidate_executed\":false}\n"
    flag (String.concat "," (List.map cache caches))
    (String.concat "," (List.map (fun id -> string_of_int (Hashtbl.find reads id)) identifiers)))
