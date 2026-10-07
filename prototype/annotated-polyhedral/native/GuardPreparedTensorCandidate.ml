(* The user supplies source and phase options, never a target Loop. All candidate
   loops here come from the extracted PolCert prepared code generator. *)
include GuardTensorLiteralRegionCandidate
module Pipeline = GuardMemoryPreparedPipeline
module M = GuardMemoryInstr
module L = GuardMemoryLoops.L
let invocations = ref 0
let root () = match Sys.getenv_opt "GUARDCERT_PIPELINE_DUMP" with
  | Some path -> path | None -> Filename.get_temp_dir_name ()
let rec mkdir path = if not (Sys.file_exists path) then begin
  let parent = Filename.dirname path in if parent <> path then mkdir parent;
  Unix.mkdir path 0o700
end
let emit path text = let channel = open_out path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel text)
let rec loop_expression = function
  | L.Constant z -> integer_text z | L.Var n -> "v" ^ string_of_int (GuardOpenScopIO.nat_to_int n)
  | L.Sum (a,b) -> "(" ^ loop_expression a ^ "+" ^ loop_expression b ^ ")"
  | L.Mult (k,e) -> "(" ^ integer_text k ^ "*" ^ loop_expression e ^ ")"
  | L.Div (e,k) -> "floordiv(" ^ loop_expression e ^ "," ^ integer_text k ^ ")"
  | L.Mod (e,k) -> "mod(" ^ loop_expression e ^ "," ^ integer_text k ^ ")"
  | L.Max (a,b) -> "max(" ^ loop_expression a ^ "," ^ loop_expression b ^ ")"
  | L.Min (a,b) -> "min(" ^ loop_expression a ^ "," ^ loop_expression b ^ ")"
and integer_text z = Z.to_string (GuardMemoryNumbers.export_integer z)
let rec loop_test = function
  | L.LE (a,b) -> loop_expression a ^ "<=" ^ loop_expression b
  | L.EQ (a,b) -> loop_expression a ^ "=" ^ loop_expression b
  | L.And (a,b) -> "(" ^ loop_test a ^ " && " ^ loop_test b ^ ")"
  | L.Or (a,b) -> "(" ^ loop_test a ^ " || " ^ loop_test b ^ ")"
  | L.Not a -> "!(" ^ loop_test a ^ ")" | L.TConstantTest b -> string_of_bool b
let rec statement indent = function
  | L.Loop (lower,upper,body) -> indent ^ "loop [" ^ loop_expression lower ^ "," ^ loop_expression upper ^ ")\n" ^ statement (indent ^ "  ") body
  | L.Guard (test,body) -> indent ^ "guard " ^ loop_test test ^ "\n" ^ statement (indent ^ "  ") body
  | L.Instr (instruction,args) -> indent ^ "instruction array=" ^
      Z.to_string (GuardMemoryNumbers.export_positive (fst instruction.M.instruction_write)) ^
      " args=(" ^ String.concat "," (List.map loop_expression args) ^ ")\n"
  | L.Seq statements -> statements_text indent statements
and statements_text indent = function
  | L.SNil -> indent ^ "skip\n"
  | L.SCons (head,tail) -> statement indent head ^ statements_text indent tail
let run path before =
  try
    let input = Filename.concat path "before.scop" in
    GuardOpenScopIO.write input before;
    let binary = match Sys.getenv_opt "GUARDCERT_PLUTO" with Some path -> path | None -> "pluto" in
    let mode = Option.value (Sys.getenv_opt "GUARDCERT_POLYHEDRAL_MODE") ~default:"affine" in
    let flags = ["--readscop";"--dumpscop";"--notile";
      "--nodiamond-tile";"--noprevector";"--nounrolljam";"--noparallel";"--smartfuse"] in
    let flags = if mode="identity" then "--identity"::"--nointratileopt"::flags
      else "--intratileopt"::flags in
    let command = "/usr/bin/timeout" in
    let arguments = Array.of_list (command::"60"::binary::flags@[input]) in
    emit (Filename.concat path "command.txt") (String.concat "\n" (Array.to_list arguments) ^ "\n");
    let log = Unix.openfile (Filename.concat path "scheduler.log") [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_TRUNC] 0o600 in
    let cwd = Sys.getcwd () in
    let status = Fun.protect ~finally:(fun () -> Unix.chdir cwd; Unix.close log) (fun () ->
      Unix.chdir path;
      let process = Unix.create_process command arguments Unix.stdin log log in snd (Unix.waitpid [] process)) in
    (match status with Unix.WEXITED 0 -> () | _ -> failwith "scheduler process failed");
    Result.Okk (GuardOpenScopIO.read before (input ^ ".afterscheduling.scop"))
  with error ->
    let reason = match error with
      | Invalid_argument reason | Failure reason | Sys_error reason -> reason
      | End_of_file -> "truncated OpenScop output"
      | Not_found -> "missing OpenScop relation or array"
      | Unix.Unix_error (error,call,_) -> call ^ ": " ^ Unix.error_message error
      | _ -> raise error in
    emit (Filename.concat path "scheduler-refusal.txt") (reason ^ "\n"); Result.Err reason
let first_instruction code =
  let rec find depth = function
    | L.Instr (_,args) -> Some (depth,args)
    | L.Loop (_,_,body) -> find (depth+1) body | L.Guard (_,body) -> find depth body
    | L.Seq body -> sequence depth body
  and sequence depth = function L.SNil -> None | L.SCons (head,tail) ->
    match find depth head with Some result -> Some result | None -> sequence depth tail in
  find 0 code
let reindex code = match first_instruction code with
  | Some (3,L.Var i::L.Var j::L.Var k::_) ->
    let coordinates = List.map GuardOpenScopIO.nat_to_int [i;j;k] in
    if List.sort compare coordinates <> [0;1;2] then None else
      (* Propose adjacent swaps for the generated axis permutation. This is
         witness data; the extracted mapped-domain checker validates it. *)
      let target = Array.of_list (List.map fst (List.sort
        (fun (_,a) (_,b) -> compare b a) (List.mapi (fun axis v -> axis,v) coordinates))) in
      let current = [|0;1;2|] and steps = ref [] in
      for axis = 0 to 2 do
        let position = ref axis in
        while current.(!position) <> target.(axis) do incr position done;
        while !position > axis do
          let left = !position-1 in
          let saved = current.(left) in current.(left) <- current.(!position); current.(!position) <- saved;
          steps := GuardMemoryAffineReindex.MemoryReindexSwap (nat left)::!steps;
          decr position
        done
      done;
      Some (List.rev !steps)
  | _ -> None
let propose instructions =
  if mode () = "disabled" then None else try
    incr invocations;
    let path = Filename.concat (root ()) (Printf.sprintf "guardcert-phase-%d-%d" (Unix.getpid ()) !invocations) in
    mkdir path;
    let path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
    let arrays = List.sort_uniq compare (List.concat_map (fun instruction ->
      List.map fst (instruction.M.instruction_write::instruction.M.instruction_reads)) instructions) in
    let maximum = List.fold_left (fun maximum id -> Z.max maximum (GuardMemoryNumbers.export_positive id)) Z.one arrays in
    let context = List.init 5 (fun index -> GuardMemoryNumbers.import_positive (Z.add maximum (Z.of_int (index+1)))) in
    (* Export the parametric canonical source, without the host's machine-word
       profile guard. The final certified source/candidate factory supplies
       that profile to BOTH models; it does not rely on scheduler arithmetic.
       In particular, Pluto's signed-int matrix reader cannot represent the
       +2147483648 bias of a signed32 minimum-bound constraint. *)
    let code = GuardMemoryScalarLoops.memory_scalar_rectangle (nat 0) (nat 3) (nat 2) instructions in
    let source = ((code,context),List.map (fun id -> id,()) (context@arrays)) in
    emit (Filename.concat path "source.loop") (statement "" code);
    let outcome = ref None in
    ImpureConfig.Core.Base.bind (Pipeline.checked_memory_prepared_loop (run path) source)
      (fun result -> outcome := Some result; ());
    match !outcome with
    | Some (Some ((generated,_),_),true) ->
      emit (Filename.concat path "generated.loop") (statement "" generated);
      emit (Filename.concat path "pipeline-result.txt") "phase-validation=accepted\nprepared-codegen=successful\n";
      (match reindex generated with Some steps ->
        emit (Filename.concat path "receipt.txt") "phase-validation=accepted\nprepared-codegen=successful\n";
        Some (ClightTensorRegionPreservation.TensorRegionMapped (generated,steps))
       | None -> emit (Filename.concat path "refusal.txt") "generated coordinate reindex outside current bridge\n"; None)
    | _ -> emit (Filename.concat path "refusal.txt") "pipeline refused or alarmed\n"; None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
