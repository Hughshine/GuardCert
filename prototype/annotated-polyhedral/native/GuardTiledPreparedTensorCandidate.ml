(* The user supplies source and phase options, never a target Loop. All candidate
   loops here come from the extracted PolCert prepared code generator. *)
include GuardTensorLiteralRegionCandidate
module Pipeline = GuardMemoryTiledPreparedPipeline
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
let configured_mode () = Option.value (Sys.getenv_opt "GUARDCERT_POLYHEDRAL_MODE") ~default:"tile"
let sizes () =
  let value = Option.value (Sys.getenv_opt "GUARDCERT_TILE_SIZES") ~default:"2,3,2" in
  let sizes = String.split_on_char ',' value |> List.map int_of_string in
  if List.length sizes <> 3 || List.exists (fun n -> n<=0 || n>1024) sizes then invalid_arg "three positive bounded tile sizes required";
  sizes
let infer_witness before after =
  let open OpenScop in
  let open TilingWitness in
  let point = GuardOpenScopIO.nat_to_int before.domain.meta.out_dim_nb in
  let total = GuardOpenScopIO.nat_to_int after.domain.meta.out_dim_nb in
  let added = total-point in
  let params = GuardOpenScopIO.nat_to_int before.domain.meta.param_nb in
  if point<>3 || added<>3 || GuardOpenScopIO.nat_to_int after.domain.meta.param_nb<>params then
    invalid_arg "tiling point space outside the current bridge";
  let rows = List.map (fun (inequality,row)->inequality,List.map GuardMemoryNumbers.export_integer row) after.domain.constrs in
  let links = List.init added (fun prefix ->
    let lower = List.find (fun (inequality,row) ->
      inequality && List.length row=total+params+1 && Z.sign(List.nth row prefix)<0 &&
      List.for_all (fun axis -> axis=prefix || Z.equal(List.nth row axis)Z.zero) (List.init added Fun.id) &&
      List.for_all (fun axis -> Z.equal(List.nth row (added+axis)) (if axis=prefix then Z.one else Z.zero)) (List.init point Fun.id) &&
      List.for_all (fun index -> Z.equal(List.nth row (total+index))Z.zero) (List.init params Fun.id) &&
      Z.equal(List.nth row (total+params))Z.zero) rows |> snd in
    let size = Z.neg(List.nth lower prefix) in
    let upper = List.map Z.neg (List.filteri (fun index _ -> index<total+params) lower)@[Z.pred size] in
    if not (List.exists (fun (inequality,row)->inequality && row=upper) rows) then invalid_arg "missing matching tile interval";
    let expr = {ae_var_coeffs=List.init (prefix+point) (fun index -> integer(Z.of_int(if index=prefix+prefix then 1 else 0)));
      ae_param_coeffs=List.init params (fun _->integer Z.zero); ae_const=integer Z.zero} in
    {tl_expr=expr;tl_tile_size=GuardMemoryNumbers.import_integer size}) in
  {stw_point_dim=nat point;stw_links=links}
let run path before =
  try
    let input = Filename.concat path "before.scop" in
    GuardOpenScopIO.write input before;
    let binary = match Sys.getenv_opt "GUARDCERT_PLUTO" with Some path -> path | None -> "pluto" in
    let tiling = configured_mode ()="tile" in
    if tiling then emit (Filename.concat path "tile.sizes") (String.concat "\n" (List.map string_of_int (sizes ()))^"\n");
    let flags = ["--readscop";"--dumpscop";"--identity";"--nointratileopt";
      "--nodiamond-tile";"--noprevector";"--nounrolljam";"--noparallel";"--smartfuse";
      (if tiling then "--tile" else "--notile")] in
    let command = "/usr/bin/timeout" in
    let arguments = Array.of_list(command::"60"::binary::flags@[input]) in
    emit(Filename.concat path "command.txt")(String.concat "\n" (Array.to_list arguments)^"\n");
    let log=Unix.openfile(Filename.concat path "scheduler.log")[Unix.O_WRONLY;Unix.O_CREAT;Unix.O_TRUNC]0o600 in
    let cwd=Sys.getcwd() in
    let status=Fun.protect ~finally:(fun()->Unix.chdir cwd;Unix.close log)(fun()->
      Unix.chdir path;let process=Unix.create_process command arguments Unix.stdin log log in snd(Unix.waitpid [] process)) in
    (match status with Unix.WEXITED 0->()|_->failwith "scheduler process failed");
    let middle=GuardOpenScopIO.read before(input^".midtransform.scop") in
    let after=GuardOpenScopIO.read before(input^".afterscheduling.scop") in
    let witnesses=if tiling then List.map2 infer_witness middle.OpenScop.statements after.OpenScop.statements else List.map (fun statement ->
      {TilingWitness.stw_point_dim=statement.OpenScop.domain.meta.out_dim_nb;stw_links=[]}) middle.OpenScop.statements in
    emit(Filename.concat path "witness.txt")(String.concat "\n" (List.map(fun w ->
      "point-dim="^string_of_int(GuardOpenScopIO.nat_to_int w.TilingWitness.stw_point_dim)^" tile-sizes="^
      String.concat "," (List.map(fun link->integer_text link.TilingWitness.tl_tile_size)w.TilingWitness.stw_links))witnesses)^"\n");
    Result.Okk((middle,after),witnesses)
  with error ->
    let reason=match error with
      | Invalid_argument reason | Failure reason | Sys_error reason -> reason
      | End_of_file -> "truncated OpenScop output" | Not_found -> "missing tiling interval or relation"
      | Unix.Unix_error(error,call,_) -> call^": "^Unix.error_message error
      | _ -> raise error in
    emit(Filename.concat path "scheduler-refusal.txt")(reason^"\n");Result.Err reason
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
let diagnose path instructions context arrays generated witnesses =
  let vars=List.map(fun id->id,())(context@arrays) in
  let assumed code=GuardMemoryScalarChecker.memory_scalar_assumed_loop(nat 3)(small 32)(nat 2)code in
  let extract label code=match GuardMemoryExtractorTrace.MemoryExtractor.extractor((assumed code,context),vars) with
    | Result.Err reason->emit(Filename.concat path(label^"-extract.txt"))("error="^reason^"\n");None
    | Result.Okk((pis,_),_) as model->
      emit(Filename.concat path(label^"-extract.txt"))("instructions="^string_of_int(List.length pis)^"\n");
      (match model with Result.Okk model->
        (match GuardMemoryPreparedPipeline.export_memory_model model with Some scop->GuardOpenScopIO.write(Filename.concat path(label^"-model.scop"))scop|None->())
       | _->());Some(GuardMemoryDomainNormalization.memory_normalized_instructions pis) in
  match extract "checked-source" (GuardMemoryScalarLoops.memory_scalar_rectangle(nat 0)(nat 3)(nat 2)instructions),
    extract "checked-candidate" generated with
  | Some before,Some after->
    (match GuardMemoryExtractedTiling.memory_attach_tiling_instructions(nat(List.length context))before after witnesses with
      | None->emit(Filename.concat path "candidate-stage.txt")"attach refused\n"
      | Some tiled->
        let current=List.map(GuardMemoryPolyhedral.GuardMemoryIRs.PolyLang.current_view_pi(nat(List.length context)))tiled in
        let aligned=ref None in
        ImpureConfig.Core.Base.bind(GuardMemoryDomainAlignment.memory_align_domains current after)(fun result->aligned:=Some result;());
        emit(Filename.concat path "candidate-stage.txt")
          (Printf.sprintf "shape=%b aligned=%s\n" (GuardMemoryExtractedTiling.memory_tiling_current_shape tiled)
            (match !aligned with Some(Some aligned,free)->Printf.sprintf "some equal=%b alarm-free=%b"
              (GuardMemoryExtractedTiling.memory_pinstr_list_eqb current aligned)free
             | Some(None,free)->Printf.sprintf "none alarm-free=%b" free|None->"no result")))
  | _->()
(* Untrusted syntax adaptation, checked on the final candidate. The extractor
   handles affine guards rather than min/max/floor bounds. These functions
   preserve the generated loop skeleton and argument expressions, propose
   affine enclosures, and encode membership using positive-divisor identities.
   No correctness or enclosure assumption is trusted by the final factory. *)
let rec affine = function
  | L.Constant _ | L.Var _->true
  | L.Mult(_,e)->affine e | L.Sum(a,b)->affine a && affine b
  | _->false
let rec shift = function
  | L.Constant _ as e->e | L.Var n->L.Var(Datatypes.S n)
  | L.Sum(a,b)->L.Sum(shift a,shift b) | L.Mult(k,e)->L.Mult(k,shift e)
  | L.Div(e,k)->L.Div(shift e,k) | L.Mod(e,k)->L.Mod(shift e,k)
  | L.Max(a,b)->L.Max(shift a,shift b) | L.Min(a,b)->L.Min(shift a,shift b)
let one=L.Constant(small 1)
let rec lower_membership bound iterator = match bound with
  | L.Max(a,b)->L.And(lower_membership a iterator,lower_membership b iterator)
  | L.Div(e,d) when affine e && Z.sign(GuardMemoryNumbers.export_integer d)>0->
    L.LE(e,L.Sum(L.Mult(d,L.Sum(iterator,one)),L.Constant(small(-1))))
  | e when affine e->L.LE(e,iterator)
  | _->invalid_arg "unsupported generated lower-bound membership"
let rec upper_membership iterator bound = match bound with
  | L.Min(a,b)->L.And(upper_membership iterator a,upper_membership iterator b)
  | L.Div(e,d) when affine e && Z.sign(GuardMemoryNumbers.export_integer d)>0->
    L.LE(L.Mult(d,L.Sum(iterator,one)),e)
  | e when affine e->L.LE(L.Sum(iterator,one),e)
  | _->invalid_arg "unsupported generated upper-bound membership"
let rec upper_enclosure = function
  | L.Min(a,_)->upper_enclosure a
  | L.Div(e,d) when affine e && Z.sign(GuardMemoryNumbers.export_integer d)>0->L.Sum(e,one)
  | e when affine e->e
  | _->invalid_arg "unsupported generated affine enclosure"
let rec adapt_bounds = function
  | L.Loop(lower,upper,body) when affine lower && affine upper->L.Loop(lower,upper,adapt_bounds body)
  | L.Loop(lower,upper,body)->
    let iterator=L.Var(nat 0) in
    L.Loop((if affine lower then lower else L.Constant(small 0)),upper_enclosure upper,
      L.Guard(L.And(lower_membership(shift lower)iterator,upper_membership iterator(shift upper)),adapt_bounds body))
  | L.Guard(test,body)->L.Guard(test,adapt_bounds body)
  | L.Instr _ as body->body
  | L.Seq body->L.Seq(adapt_sequence body)
and adapt_sequence = function L.SNil->L.SNil|L.SCons(head,tail)->L.SCons(adapt_bounds head,adapt_sequence tail)
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
    ImpureConfig.Core.Base.bind (Pipeline.checked_memory_tiled_prepared_loop (run path) source)
      (fun result -> outcome := Some result; ());
    match !outcome with
    | Some (Some (((generated,_),_),witnesses),true) ->
      emit (Filename.concat path "raw-generated.loop") (statement "" generated);
      let generated=adapt_bounds generated in
      emit (Filename.concat path "generated.loop") (statement "" generated);
      emit (Filename.concat path "pipeline-result.txt") "phase-validation=accepted\nprepared-codegen=successful\n";
      if Sys.getenv_opt "GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS"=Some "1" then begin
        diagnose path instructions context arrays generated witnesses;
        let checked=ref None in
        ImpureConfig.Core.Base.bind
          (Pipeline.checked_memory_scalar_generated_tiling (nat 3) (small 32) (nat 2)
            instructions context arrays generated witnesses)
          (fun result -> checked:=Some result; ());
        emit(Filename.concat path "candidate-domain-check.txt")
          (match !checked with Some(valid,alarm_free)->Printf.sprintf "valid=%b alarm-free=%b\n" valid alarm_free
            | None->"no result\n")
      end;
      if List.exists(fun w -> w.TilingWitness.stw_links <> [])witnesses then begin
        emit (Filename.concat path "receipt.txt") "affine-validation=accepted\ntiling-validation=accepted\nprepared-codegen=successful\nbound-adaptation=proposed\nactual-candidate-check=pending\n";
        Some (ClightTensorGeneratedCandidates.TensorGeneratedTiled (generated,witnesses))
      end else (match reindex generated with
        | Some steps -> Some (ClightTensorGeneratedCandidates.TensorGeneratedMapped (generated,steps))
        | None -> emit (Filename.concat path "refusal.txt") "generated coordinate reindex outside current bridge\n"; None)

    | _ -> emit (Filename.concat path "refusal.txt") "pipeline refused or alarmed\n"; None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
