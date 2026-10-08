(* Coordinate proposals for actual prepared output. All proposals, including
   singleton-loop completion and operand rebinding, are untrusted and rechecked
   by the existing actual source/candidate factory. *)
include GuardTightPreparedTensorCandidate

let rec lift_expression cutoff = function
  | L.Constant _ as e -> e
  | L.Var n -> if GuardOpenScopIO.nat_to_int n >= cutoff then L.Var(Datatypes.S n) else L.Var n
  | L.Sum(a,b) -> L.Sum(lift_expression cutoff a,lift_expression cutoff b)
  | L.Mult(k,e) -> L.Mult(k,lift_expression cutoff e)
  | L.Div(e,k) -> L.Div(lift_expression cutoff e,k)
  | L.Mod(e,k) -> L.Mod(lift_expression cutoff e,k)
  | L.Max(a,b) -> L.Max(lift_expression cutoff a,lift_expression cutoff b)
  | L.Min(a,b) -> L.Min(lift_expression cutoff a,lift_expression cutoff b)
let rec lift_test cutoff = function
  | L.LE(a,b) -> L.LE(lift_expression cutoff a,lift_expression cutoff b)
  | L.EQ(a,b) -> L.EQ(lift_expression cutoff a,lift_expression cutoff b)
  | L.And(a,b) -> L.And(lift_test cutoff a,lift_test cutoff b)
  | L.Or(a,b) -> L.Or(lift_test cutoff a,lift_test cutoff b)
  | L.Not test -> L.Not(lift_test cutoff test)
  | L.TConstantTest _ as test -> test
let rec lift_statement cutoff = function
  | L.Loop(lo,hi,body) -> L.Loop(lift_expression cutoff lo,lift_expression cutoff hi,lift_statement(cutoff+1)body)
  | L.Guard(test,body) -> L.Guard(lift_test cutoff test,lift_statement cutoff body)
  | L.Instr(instruction,args) -> L.Instr(instruction,List.map(lift_expression cutoff)args)
  | L.Seq sequence -> L.Seq(lift_sequence cutoff sequence)
and lift_sequence cutoff = function
  | L.SNil -> L.SNil
  | L.SCons(head,tail) -> L.SCons(lift_statement cutoff head,lift_sequence cutoff tail)

let unit_axes witnesses =
  let mask witness =
    if GuardOpenScopIO.nat_to_int witness.TilingWitness.stw_point_dim <> 3 ||
       List.length witness.TilingWitness.stw_links <> 3 then
      invalid_arg "unit completion requires three point axes and tile links";
    List.map(fun link -> Z.equal(GuardMemoryNumbers.export_integer link.TilingWitness.tl_tile_size)Z.one)
      witness.TilingWitness.stw_links in
  match witnesses with
  | [] -> invalid_arg "missing tiling witness"
  | first::rest -> let units=mask first in
    if not(List.for_all(fun witness -> mask witness=units)rest) then invalid_arg "incompatible unit axes";
    units

let validate_point_slots units code =
  let nonunit=List.filter(fun axis -> not(List.nth units axis))[0;1;2] in
  let expected_depth=3+List.length nonunit in
  let rank axis =
    let rec find i = function a::_ when a=axis -> i | _::rest -> find(i+1)rest | [] -> assert false in
    find 0 nonunit in
  let positions=List.init 3(fun axis -> expected_depth-1-
    (if List.nth units axis then axis else 3+rank axis)) in
  let rec check depth = function
    | L.Loop(_,_,body) -> check(depth+1)body
    | L.Guard(_,body) -> check depth body
    | L.Instr(_,L.Var i::L.Var j::L.Var k::_) ->
      if depth<>expected_depth || List.map GuardOpenScopIO.nat_to_int [i;j;k]<>positions then
        invalid_arg "generated coordinate order outside unit completion"
    | L.Instr _ -> invalid_arg "non-variable source coordinates"
    | L.Seq sequence -> check_sequence depth sequence
  and check_sequence depth = function
    | L.SNil -> ()
    | L.SCons(head,tail) -> check depth head;check_sequence depth tail in
  check 0 code

let complete_unit_points units code =
  validate_point_slots units code;
  let rec complete depth axis code =
    if depth>=3 && axis<3 && List.nth units axis then
      let lo=L.Var(nat(depth-1-axis))in
      L.Loop(lo,L.Sum(lo,one),complete(depth+1)(axis+1)(lift_statement 0 code))
    else match code with
    | L.Loop(lo,hi,body) when depth<3 -> L.Loop(lo,hi,complete(depth+1)axis body)
    | L.Loop(lo,hi,body) when axis<3 -> L.Loop(lo,hi,complete(depth+1)(axis+1)body)
    | L.Guard(test,body) -> L.Guard(test,complete depth axis body)
    | L.Instr(instruction,_::_::_::rest) when depth=6 && axis=3 ->
      L.Instr(instruction,L.Var(nat 2)::L.Var(nat 1)::L.Var(nat 0)::rest)
    | L.Seq sequence -> L.Seq(complete_sequence depth axis sequence)
    | _ -> invalid_arg "generated loop skeleton outside unit completion"
  and complete_sequence depth axis = function
    | L.SNil -> L.SNil
    | L.SCons(head,tail) -> L.SCons(complete depth axis head,complete_sequence depth axis tail) in
  complete 0 0 code

let propose instructions =
  if mode()="disabled" then None else try
    incr invocations;
    let path=Filename.concat(root())(Printf.sprintf "guardcert-phase-%d-%d" (Unix.getpid())!invocations)in
    mkdir path;
    let path=if Filename.is_relative path then Filename.concat(Sys.getcwd())path else path in
    let arrays=List.sort_uniq compare(List.concat_map(fun instruction ->
      List.map fst(instruction.M.instruction_write::instruction.M.instruction_reads))instructions)in
    let maximum=List.fold_left(fun largest id -> Z.max largest(GuardMemoryNumbers.export_positive id))Z.one arrays in
    let context=List.init 5(fun index -> GuardMemoryNumbers.import_positive(Z.add maximum(Z.of_int(index+1))))in
    let code=GuardMemoryScalarLoops.memory_scalar_rectangle(nat 0)(nat 3)(nat 2)instructions in
    let source=((code,context),List.map(fun id -> id,())(context@arrays))in
    emit(Filename.concat path "source.loop")(statement "" code);
    let outcome=ref None in
    ImpureConfig.Core.Base.bind(Pipeline.checked_memory_tiled_prepared_loop(run path)source)
      (fun result -> outcome:=Some result;());
    match !outcome with
    | Some(Some(((raw,_),_),witnesses),true) ->
      emit(Filename.concat path "raw-generated.loop")(statement "" raw);
      let tiled=List.exists(fun w -> w.TilingWitness.stw_links<>[])witnesses in
      let units=if tiled then unit_axes witnesses else [false;false;false]in
      let all_unit=tiled && List.for_all Fun.id units in
      let partial=tiled && not all_unit && List.exists Fun.id units in
      let completed=if partial then complete_unit_points units raw else raw in
      emit(Filename.concat path "completed.loop")(statement "" completed);
      let generated=adapt_bounds completed in
      emit(Filename.concat path "generated.loop")(statement "" generated);
      emit(Filename.concat path "pipeline-result.txt")"phase-validation=accepted\nprepared-codegen=successful\n";
      let kind=if all_unit || not tiled then "mapped" else "tiled" in
      let proposal=if kind="mapped" then match reindex generated with
        | Some steps -> ClightTensorGeneratedCandidates.TensorGeneratedMapped(generated,steps)
        | None -> invalid_arg "generated affine coordinate reindex refused"
        else ClightTensorGeneratedCandidates.TensorGeneratedTiled(generated,witnesses)in
      emit(Filename.concat path "coordinate-completion.txt")
        (Printf.sprintf "unit-axes=%s\nsingleton-completion=%b\ncandidate-kind=%s\n"
          (String.concat "," (List.map string_of_bool units))partial kind);
      if Sys.getenv_opt "GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS"=Some "1" then begin
        let checked=ref None in
        let check=match proposal with
          | ClightTensorGeneratedCandidates.TensorGeneratedMapped(_,steps) ->
            GuardMemoryScalarChecker.checked_memory_scalar_candidate(nat 3)(small 32)(nat 2)
              instructions context arrays generated steps
          | ClightTensorGeneratedCandidates.TensorGeneratedTiled(_,data) ->
            diagnose path instructions context arrays generated data;
            Pipeline.checked_memory_scalar_generated_tiling(nat 3)(small 32)(nat 2)
              instructions context arrays generated data in
        ImpureConfig.Core.Base.bind check(fun result -> checked:=Some result;());
        emit(Filename.concat path "candidate-domain-check.txt")
          (match !checked with Some(valid,free) -> Printf.sprintf "valid=%b alarm-free=%b\n" valid free
           | None -> "no result\n")
      end;
      emit(Filename.concat path "receipt.txt")
        ("affine-validation=accepted\ntiling-validation=accepted\nprepared-codegen=successful\ncoordinate-completion=proposed\nbound-adaptation=proposed\ncandidate-kind="^kind^"\nactual-candidate-check=pending\n");
      Some proposal
    | _ -> emit(Filename.concat path "refusal.txt")"pipeline refused or alarmed\n";None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
