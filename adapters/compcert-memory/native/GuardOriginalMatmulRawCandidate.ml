(* Untrusted scheduling transport for the proved literal-frontend original-double compiler.
   Every returned schedule and final generated Loop is checked by extracted
   Rocq code. Diagnostics count actual installed guarded statements. *)
let mode () = Option.value (Sys.getenv_opt "GUARDCERT_ORIGINAL_MODE") ~default:"affine"
let nat = GuardOpenScopIO.nat
let swaps () = if mode () = "affine" then [nat 1] else []
let calls = ref 0
let emit path text =
  let channel = open_out path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel text)
let reverse relation =
  let metadata = relation.OpenScop.meta in
  let first = GuardOpenScopIO.nat_to_int metadata.OpenScop.out_dim_nb in
  let last = first + GuardOpenScopIO.nat_to_int metadata.OpenScop.in_dim_nb in
  { relation with OpenScop.constrs = List.map (fun (inequality,row) -> inequality,
      List.mapi (fun index value -> if first <= index && index < last then
        GuardMemoryNumbers.import_integer (Z.neg (GuardMemoryNumbers.export_integer value)) else value) row)
      relation.OpenScop.constrs }
let schedule before =
  incr calls;
  let selected = mode () in
  Printf.eprintf "GUARDCERT_ORIGINAL_PIPELINE call=%d mode=%s\n%!" !calls selected;
  if selected = "refuse" then Result.Err "requested external refusal" else
  try
    let root = Sys.getenv "GUARDCERT_ORIGINAL_OUTPUT" in
    let path = Filename.concat root (Printf.sprintf "pipeline-%d" !calls) in
    Unix.mkdir path 0o700;
    let input = Filename.concat path "before.scop" in
    GuardOpenScopIO.write input before;
    let binary = Sys.getenv "GUARDCERT_PLUTO" in
    let flags = ["--readscop";"--dumpscop";"--notile";"--nodiamond-tile";
      "--noprevector";"--nounrolljam";"--noparallel";"--smartfuse"] in
    let flags = if selected = "affine" || selected = "wrong-witness" then "--intratileopt"::flags
      else "--identity"::"--nointratileopt"::flags in
    let command = "/usr/bin/timeout" in
    let arguments = Array.of_list (command::"60"::binary::flags@[input]) in
    emit (Filename.concat path "command.txt") (String.concat "\n" (Array.to_list arguments)^"\n");
    let output = Unix.openfile (Filename.concat path "scheduler.log") [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_EXCL] 0o600 in
    let cwd = Sys.getcwd () in
    let status = Fun.protect ~finally:(fun () -> Unix.chdir cwd; Unix.close output) (fun () ->
      Unix.chdir path;
      let pid = Unix.create_process command arguments Unix.stdin output output in snd (Unix.waitpid [] pid)) in
    (match status with Unix.WEXITED 0 -> () | _ -> failwith "Pluto execution failed");
    let after = GuardOpenScopIO.read before (input^".afterscheduling.scop") in
    let after = if selected = "reverse" then { after with OpenScop.statements =
      List.map (fun statement -> { statement with OpenScop.scattering = reverse statement.OpenScop.scattering })
        after.OpenScop.statements }
      else if selected = "malformed" then { after with OpenScop.statements = [] } else after in
    Result.Okk after
  with (Failure _ | Invalid_argument _ | Sys_error _ | Not_found | Unix.Unix_error _) as error ->
    let reason = match error with Not_found -> "missing scheduler configuration" | _ -> Printexc.to_string error in
    Printf.eprintf "GUARDCERT_ORIGINAL_REFUSED reason=%S\n%!" reason;
    Result.Err reason

let rec guarded_statement = function
  | Clight.Ssequence (capture,Clight.Sifthenelse (_,_,fallback))
    when capture = OriginalMatmulCapture.original_matmul_capture_code &&
         fallback = OriginalMatmulRawSource.raw_original_matmul_region -> 1
  | Clight.Ssequence (first,second) | Clight.Sloop (first,second) -> guarded_statement first + guarded_statement second
  | Clight.Sifthenelse (_,yes,no) -> guarded_statement yes + guarded_statement no
  | Clight.Slabel (_,body) -> guarded_statement body
  | Clight.Sswitch (_,cases) -> guarded_cases cases
  | _ -> 0
and guarded_cases = function
  | Clight.LSnil -> 0
  | Clight.LScons (_,body,rest) -> guarded_statement body + guarded_cases rest
let trace_clight program =
  let installed = List.fold_left (fun count (_,definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) -> count + guarded_statement fn.Clight.fn_body
    | _ -> count) 0 program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_ORIGINAL_INSTALLED regions=%d pipeline_calls=%d\n%!" installed !calls
