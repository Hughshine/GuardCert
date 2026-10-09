(* Untrusted real Pluto tiling transport for the checked double compiler.
   Phase data and the final adapted Loop are validated by extracted Rocq code. *)
module L = GuardMemoryDoublePolyhedral.DoubleAssignmentIRs.Loop
module M = GuardMemoryValueInstr
let nat = GuardOpenScopDoubleIO.nat
let integer = GuardMemoryNumbers.import_integer
let small n = integer (Z.of_int n)
let emit = GuardSelectedDoubleCandidate.emit
let calls = ref 0
let adaptations = ref 0
let current_path = ref None
let mode () = Option.value (Sys.getenv_opt "GUARDCERT_DOUBLE_TILING_MODE")
  ~default:(if GuardSelectedDoubleCandidate.mode () = "tile" then "tile" else "disabled")
let enabled () = mode () <> "disabled"
let private_count = GuardSelectedDoubleWitnessPolicy.private_count
let choices = GuardSelectedDoubleWitnessPolicy.choices
let legacy_schedule before = if enabled () then Result.Err "tiling refusal retains original source"
  else GuardSelectedDoubleWitnessPolicy.schedule before
let rec loop_expression = function
  | L.Constant z -> integer_text z | L.Var n -> "v" ^ string_of_int (GuardOpenScopDoubleIO.nat_to_int n)
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
      Z.to_string (GuardMemoryNumbers.export_positive (fst instruction.M.value_instruction_write)) ^
      " args=(" ^ String.concat "," (List.map loop_expression args) ^ ")\n"
  | L.Seq statements -> statements_text indent statements
and statements_text indent = function
  | L.SNil -> indent ^ "skip\n"
  | L.SCons (head,tail) -> statement indent head ^ statements_text indent tail
let infer_witness before after =
  let open OpenScop in
  let open TilingWitness in
  let point = GuardOpenScopDoubleIO.nat_to_int before.domain.meta.out_dim_nb in
  let total = GuardOpenScopDoubleIO.nat_to_int after.domain.meta.out_dim_nb in
  let added = total-point in
  let params = GuardOpenScopDoubleIO.nat_to_int before.domain.meta.param_nb in
  if point<=0 || added<>point || GuardOpenScopDoubleIO.nat_to_int after.domain.meta.param_nb<>params then
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
let sizes dimensions =
  let text=Option.value(Sys.getenv_opt "GUARDCERT_TILE_SIZES")~default:"32" in
  let values=String.split_on_char ',' text |> List.map int_of_string in
  let values=match values with [size]->List.init dimensions(fun _->size)|values->values in
  if List.length values<>dimensions || List.exists(fun n->n<=0 || n>1024)values
  then invalid_arg "one or rank-many positive tile sizes required";
  values
let phase before = if not(enabled()) then Result.Err "double tiling disabled" else
  let path=ref None in
  try
    incr calls;
    Printf.eprintf "GUARDCERT_DOUBLE_TILING_PIPELINE call=%d mode=%s\n%!" !calls (mode());
    let directory=Filename.concat(Sys.getenv "GUARDCERT_ORIGINAL_OUTPUT")
      (Printf.sprintf "tiling-pipeline-%d" !calls) in
    Unix.mkdir directory 0o700; path:=Some directory; current_path:=Some directory;
    let input=Filename.concat directory "before.scop" in
    GuardOpenScopDoubleIO.write input before;
    if mode()="refuse" then failwith "requested external tiling refusal";
    let dimensions=List.fold_left(fun n s->max n
      (GuardOpenScopDoubleIO.nat_to_int s.OpenScop.domain.meta.out_dim_nb))0 before.OpenScop.statements in
    emit(Filename.concat directory "tile.sizes")
      (String.concat "\n" (List.map string_of_int(sizes dimensions))^"\n");
    let flags=["--readscop";"--dumpscop";"--identity";"--nointratileopt";"--tile";
      "--nodiamond-tile";"--noprevector";"--nounrolljam";"--noparallel";"--smartfuse"] in
    let command="/usr/bin/timeout" in
    let arguments=Array.of_list(command::"60"::Sys.getenv "GUARDCERT_PLUTO"::flags@[input]) in
    emit(Filename.concat directory "command.txt")(String.concat "\n" (Array.to_list arguments)^"\n");
    let log=Unix.openfile(Filename.concat directory "scheduler.log")
      [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_EXCL]0o600 in
    let cwd=Sys.getcwd() in
    let status=Fun.protect ~finally:(fun()->Unix.chdir cwd;Unix.close log)(fun()->
      Unix.chdir directory;let pid=Unix.create_process command arguments Unix.stdin log log in snd(Unix.waitpid []pid)) in
    (match status with Unix.WEXITED 0->()|_->failwith "Pluto tiling failed");
    let middle=GuardOpenScopDoubleIO.read before(input^".midtransform.scop") in
    let after=GuardOpenScopDoubleIO.read before(input^".afterscheduling.scop") in
    let witnesses=List.map2 infer_witness middle.OpenScop.statements after.OpenScop.statements in
    let witnesses=if mode()="wrong-witness" then List.map(fun w->{w with TilingWitness.stw_links=[]})witnesses else witnesses in
    let after=if mode()="malformed" then {after with OpenScop.statements=[]} else after in
    emit(Filename.concat directory "witness.txt")(String.concat "\n" (List.map(fun w->
      "point-dim="^string_of_int(GuardOpenScopDoubleIO.nat_to_int w.TilingWitness.stw_point_dim)^" tile-sizes="^
      String.concat "," (List.map(fun link->integer_text link.TilingWitness.tl_tile_size)w.TilingWitness.stw_links))witnesses)^"\n");
    Result.Okk((middle,after),witnesses)
  with (Invalid_argument _ | Failure _ | Sys_error _ | Not_found | End_of_file | Unix.Unix_error _) as error->
    let reason=Printexc.to_string error in
    (match !path with Some directory->emit(Filename.concat directory "refusal.txt")(reason^"\n")|None->());
    Printf.eprintf "GUARDCERT_DOUBLE_TILING_REFUSED reason=%S\n%!" reason; Result.Err reason
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
  | L.Sum(e,L.Constant c) when not (affine e)->
    lower_membership e (L.Sum(iterator,L.Constant(GuardMemoryNumbers.import_integer(Z.neg(GuardMemoryNumbers.export_integer c)))))
  | L.Div(e,d) when affine e && Z.sign(GuardMemoryNumbers.export_integer d)>0->
    L.LE(e,L.Sum(L.Mult(d,L.Sum(iterator,one)),L.Constant(small(-1))))
  | e when affine e->L.LE(e,iterator)
  | _->invalid_arg "unsupported generated lower-bound membership"
let rec upper_membership iterator bound = match bound with
  | L.Min(a,b)->L.And(upper_membership iterator a,upper_membership iterator b)
  | L.Sum(e,L.Constant c) when not (affine e)->
    upper_membership (L.Sum(iterator,L.Constant(GuardMemoryNumbers.import_integer(Z.neg(GuardMemoryNumbers.export_integer c))))) e
  | L.Div(e,d) when affine e && Z.sign(GuardMemoryNumbers.export_integer d)>0->
    L.LE(L.Mult(d,L.Sum(iterator,one)),e)
  | e when affine e->L.LE(L.Sum(iterator,one),e)
  | _->invalid_arg "unsupported generated upper-bound membership"
let rec max_leaves = function L.Max(a,b)->max_leaves a @ max_leaves b | e->[e]
let rec min_leaves = function L.Min(a,b)->min_leaves a @ min_leaves b | e->[e]
let rec score depth = function
  | L.Var n->if GuardOpenScopDoubleIO.nat_to_int n<depth then 1 else 0
  | L.Sum(a,b)->score depth a+score depth b | L.Mult(_,e)->score depth e | _->0
let choose depth fallback leaves = fst(List.fold_left(fun (best,saved)e->
  let rank=if affine e then score depth e else -1 in
  if rank>saved then e,rank else best,saved)(fallback,0)leaves)
let rec upper_enclosure = function
  | L.Min(a,_)->upper_enclosure a
  | L.Sum(a,b)->L.Sum(upper_enclosure a,upper_enclosure b)
  | L.Mult(k,e) when Z.sign(GuardMemoryNumbers.export_integer k)>0->L.Mult(k,upper_enclosure e)
  | L.Div(e,d) when affine e && Z.sign(GuardMemoryNumbers.export_integer d)>0->L.Sum(e,one)
  | e when affine e->e
  | _->invalid_arg "unsupported affine upper enclosure"
let rec adapt_at depth = function
  | L.Loop(lower,upper,body) when affine lower && affine upper->
    L.Loop(lower,upper,adapt_at(depth+1)body)
  | L.Loop(lower,upper,body)->
    let lo=choose depth (if affine lower then lower else L.Constant(small 0))(max_leaves lower) in
    let hi=choose depth (upper_enclosure upper)(min_leaves upper) in
    let iterator=L.Var(nat 0) in
    L.Loop(lo,hi,L.Guard(L.And(lower_membership(shift lower)iterator,
      upper_membership iterator(shift upper)),adapt_at(depth+1)body))
  | L.Guard(test,body)->L.Guard(test,adapt_at depth body)
  | L.Instr _ as body->body
  | L.Seq sequence->L.Seq(adapt_sequence depth sequence)
and adapt_sequence depth = function L.SNil->L.SNil | L.SCons(head,tail)->
  L.SCons(adapt_at depth head,adapt_sequence depth tail)
let adapt limit ((body,context),variables) =
  incr adaptations;
  try
    let path=match !current_path with Some path->path | None->failwith "missing tiling phase receipt" in
    emit(Filename.concat path "raw-generated.loop")(statement "" body);
    emit(Filename.concat path "adaptation-limit.txt")(integer_text limit^"\n");
    let generated=adapt_at 0 body in
    emit(Filename.concat path "generated.loop")(statement "" generated);
    emit(Filename.concat path "adaptation.txt")"raw-phase-checks=accepted\nprepared-codegen=successful\nbound-adaptation=proposed\nfinal-candidate-check=pending\n";
    Result.Okk((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error->
    (match !current_path with Some path->emit(Filename.concat path "adaptation-refusal.txt")(Printexc.to_string error^"\n")|None->());
    Result.Err(Printexc.to_string error)
let trace_clight program =
  GuardSelectedDoubleWitnessPolicy.trace_clight program;
  let installed=List.fold_left(fun count(_,definition)->match definition with
    | AST.Gfun(Ctypes.Internal fn)->count+GuardSelectedReductionCandidate.reduction_count program fn.Clight.fn_body
    | _->count)0 program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_DOUBLE_TILING_INSTALLED reduction=%d phase_calls=%d adaptations=%d enabled=%b\n%!"
    installed !calls !adaptations (enabled())
