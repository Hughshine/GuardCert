(* Exercise the extracted double pipeline on the input derived from the actual
   exported source. This executable is a pipeline probe, not a C compiler. *)
module M = GuardMemoryDoublePolyhedral
module L = M.DoubleAssignmentIRs.Loop
module P = M.DoubleAssignmentIRs.PolyLang
module E = M.DoubleAssignmentExtractor
module D = GuardMemoryDoublePrepared

let integer z = Z.to_string (GuardMemoryNumbers.export_integer z)
let emit path text = let output = open_out path in
  Fun.protect ~finally:(fun () -> close_out output) (fun () -> output_string output text)
let rec expression = function
  | L.Constant z -> integer z | L.Var n -> "v" ^ string_of_int (GuardOpenScopIO.nat_to_int n)
  | L.Sum (a,b) -> "(" ^ expression a ^ "+" ^ expression b ^ ")"
  | L.Mult (k,a) -> "(" ^ integer k ^ "*" ^ expression a ^ ")"
  | L.Div (a,k) -> "floordiv(" ^ expression a ^ "," ^ integer k ^ ")"
  | L.Mod (a,k) -> "mod(" ^ expression a ^ "," ^ integer k ^ ")"
  | L.Max (a,b) -> "max(" ^ expression a ^ "," ^ expression b ^ ")"
  | L.Min (a,b) -> "min(" ^ expression a ^ "," ^ expression b ^ ")"
let rec test = function
  | L.LE (a,b) -> expression a ^ "<=" ^ expression b
  | L.EQ (a,b) -> expression a ^ "=" ^ expression b
  | L.And (a,b) -> "(" ^ test a ^ " && " ^ test b ^ ")"
  | L.Or (a,b) -> "(" ^ test a ^ " || " ^ test b ^ ")"
  | L.Not a -> "!(" ^ test a ^ ")" | L.TConstantTest b -> string_of_bool b
let rec statement indent = function
  | L.Loop (lower,upper,body) -> indent ^ "loop [" ^ expression lower ^ "," ^ expression upper ^ ")\n" ^ statement (indent ^ "  ") body
  | L.Guard (condition,body) -> indent ^ "guard " ^ test condition ^ "\n" ^ statement (indent ^ "  ") body
  | L.Instr (instruction,args) -> indent ^ "double instruction array=" ^
      Z.to_string (GuardMemoryNumbers.export_positive (fst instruction.GuardMemoryValueInstr.value_instruction_write)) ^
      " args=(" ^ String.concat "," (List.map expression args) ^ ")\n"
  | L.Seq statements -> sequence indent statements
and sequence indent = function
  | L.SNil -> indent ^ "skip\n" | L.SCons (head,tail) -> statement indent head ^ sequence indent tail
let rec instructions = function
  | L.Instr (instruction,_) -> [instruction]
  | L.Loop (_,_,body) | L.Guard (_,body) -> instructions body
  | L.Seq body -> sequence_instructions body
and sequence_instructions = function
  | L.SNil -> [] | L.SCons (head,tail) -> instructions head @ sequence_instructions tail
let describe_model model =
  let ((pis,params),_) = model in
  "parameters=" ^ String.concat "," (List.map (fun id -> Z.to_string (GuardMemoryNumbers.export_positive id)) params) ^ "\n" ^
  String.concat "" (List.mapi (fun index pi ->
    "statement=" ^ string_of_int index ^ "\n" ^
    String.concat "" (List.map (fun (coefficients,bias) ->
      "schedule " ^ String.concat "," (List.map integer coefficients) ^ ";" ^ integer bias ^ "\n") pi.P.pi_schedule)) pis)
let result_json path fields =
  emit (Filename.concat path "result.json") ("{\n" ^
    String.concat ",\n" (List.map (fun (key,value) -> Printf.sprintf "  %S: %s" key value) fields) ^ "\n}\n")
let reverse_iterators relation =
  let m = relation.OpenScop.meta in
  let start = GuardOpenScopIO.nat_to_int m.OpenScop.out_dim_nb in
  let finish = start + GuardOpenScopIO.nat_to_int m.OpenScop.in_dim_nb in
  { relation with OpenScop.constrs = List.map (fun (flag,row) -> flag,
      List.mapi (fun index value -> if index >= start && index < finish then
        GuardMemoryNumbers.import_integer (Z.neg (GuardMemoryNumbers.export_integer value)) else value) row) relation.OpenScop.constrs }
let () =
  if Array.length Sys.argv <> 4 then invalid_arg "probe PLUTO MODE NEW_OUTPUT_DIRECTORY";
  let binary,mode,path = Sys.argv.(1),Sys.argv.(2),Sys.argv.(3) in
  Unix.mkdir path 0o700;
  let source = OriginalMatmulPrepared.original_matmul_pipeline_request in
  let ((source_code,_),_) = source in
  emit (Filename.concat path "source.loop") (statement "" source_code);
  let model = match E.extractor source with Result.Okk model -> model | Result.Err reason -> failwith reason in
  emit (Filename.concat path "source.model") (describe_model model);
  let scheduler_calls = ref 0 and proposed = ref None and scheduler_error = ref None in
  let schedule before =
    incr scheduler_calls;
    GuardOpenScopIO.write (Filename.concat path "before.scop") before;
    if mode = "refuse" then begin scheduler_error := Some "requested external refusal"; Result.Err "requested external refusal" end
    else try
      let input = Filename.concat path "before.scop" in
      let flags = ["--readscop";"--dumpscop";"--notile";"--nodiamond-tile";
        "--noprevector";"--nounrolljam";"--noparallel";"--smartfuse"] in
      let flags = if mode = "affine" then "--intratileopt"::flags else "--identity"::"--nointratileopt"::flags in
      let command = "/usr/bin/timeout" in
      let arguments = Array.of_list (command::"60"::binary::flags@[input]) in
      emit (Filename.concat path "command.txt") (String.concat "\n" (Array.to_list arguments) ^ "\n");
      let output = Unix.openfile (Filename.concat path "scheduler.log") [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_EXCL] 0o600 in
      let cwd = Sys.getcwd () in
      let status = Fun.protect ~finally:(fun () -> Unix.chdir cwd; Unix.close output) (fun () ->
        Unix.chdir path;
        let pid = Unix.create_process command arguments Unix.stdin output output in snd (Unix.waitpid [] pid)) in
      (match status with Unix.WEXITED 0 -> () | _ -> failwith "Pluto execution failed");
      let after = GuardOpenScopIO.read before (input ^ ".afterscheduling.scop") in
      let after = if mode = "reverse" then { after with OpenScop.statements =
        List.map (fun stmt -> { stmt with OpenScop.scattering = reverse_iterators stmt.OpenScop.scattering }) after.OpenScop.statements }
        else if mode = "malformed" then { after with OpenScop.statements = [] } else after in
      let snapshot = open_out_bin (Filename.concat path "proposed.openscop.bin") in
      Fun.protect ~finally:(fun () -> close_out snapshot) (fun () -> Marshal.to_channel snapshot after []);
      (match P.from_openscop_like_source model after with
       | Result.Okk candidate -> proposed := Some candidate; emit (Filename.concat path "proposed.model") (describe_model candidate)
       | Result.Err reason -> emit (Filename.concat path "import-refusal.txt") (reason ^ "\n"));
      Result.Okk after
    with (Failure reason | Invalid_argument reason | Sys_error reason) ->
      scheduler_error := Some reason; emit (Filename.concat path "scheduler-refusal.txt") (reason ^ "\n"); Result.Err reason in
  let outcome = ref None in
  ImpureConfig.Core.Base.bind (D.checked_double_prepared_loop schedule source) (fun result -> outcome := Some result; ());
  let accepted,alarm_free,retained,changed = match !outcome with
    | Some (Some generated,true) ->
      let ((code,_),_) = generated in
      emit (Filename.concat path "generated.loop") (statement "" code);
      let original = instructions source_code in
      let retained = List.for_all (fun instruction -> List.mem instruction original) (instructions code) in
      true,true,retained,code <> source_code
    | Some (_,alarm_free) -> false,alarm_free,false,false
    | None -> false,false,false,false in
  let model_changed = match !proposed with Some candidate -> candidate <> model | None -> false in
  result_json path ["status",Printf.sprintf "%S" (if accepted then "accepted" else "refused");
    "mode",Printf.sprintf "%S" mode; "scheduler_calls",string_of_int !scheduler_calls;
    "alarm_free",string_of_bool alarm_free; "original_double_instructions_retained",string_of_bool retained;
    "model_changed",string_of_bool model_changed; "generated_Loop_changed",string_of_bool changed;
    "scheduler_error",(match !scheduler_error with None -> "null" | Some reason -> Printf.sprintf "%S" reason);
    "C_compiler_or_whole_program_installation","false"];
  Printf.printf "%s: %s\n%!" mode (if accepted then "accepted" else "refused")
