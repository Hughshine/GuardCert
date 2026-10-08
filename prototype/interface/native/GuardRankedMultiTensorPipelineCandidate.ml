(* Rank is source-family configuration, not a synthetic source axis. All
   generated, distributed, completed and rebound targets are checked again by
   the extracted full source/candidate factory. *)
include GuardAffineMultiTensorPipelineCandidate

let tile_sizes rank =
  let fallback=String.concat "," (List.init rank(fun i->string_of_int(i+2))) in
  let text=Option.value(Sys.getenv_opt "GUARDCERT_TILE_SIZES")~default:fallback in
  let result=List.map int_of_string(String.split_on_char ',' text) in
  if List.length result<>rank || List.exists(fun n->n<=0 || n>1024)result then
    invalid_arg "rank-sized positive bounded tiles required";
  result
let infer_ranked_witness rank before after =
  let open OpenScop in
  let open TilingWitness in
  let point=GuardOpenScopIO.nat_to_int before.domain.meta.out_dim_nb in
  let total=GuardOpenScopIO.nat_to_int after.domain.meta.out_dim_nb in
  let added=total-point in
  let parameters=GuardOpenScopIO.nat_to_int before.domain.meta.param_nb in
  if point<>rank || added<>rank ||
    GuardOpenScopIO.nat_to_int after.domain.meta.param_nb<>parameters then
    invalid_arg "unexpected tiling dimensions";
  let rows=List.map(fun (inequality,row)->inequality,List.map GuardMemoryNumbers.export_integer row)
    after.domain.constrs in
  let links=List.init added(fun prefix->
    let lower=List.find(fun (inequality,row)->
      inequality && List.length row=total+parameters+1 && Z.sign(List.nth row prefix)<0 &&
      List.for_all(fun axis->axis=prefix || Z.equal(List.nth row axis)Z.zero)(List.init added Fun.id) &&
      List.for_all(fun axis->Z.equal(List.nth row(added+axis))
        (if axis=prefix then Z.one else Z.zero))(List.init point Fun.id) &&
      List.for_all(fun index->Z.equal(List.nth row(total+index))Z.zero)(List.init parameters Fun.id) &&
      Z.equal(List.nth row(total+parameters))Z.zero)rows |> snd in
    let size=Z.neg(List.nth lower prefix) in
    let upper=List.map Z.neg(List.filteri(fun index _->index<total+parameters)lower)@[Z.pred size] in
    if not(List.exists(fun (inequality,row)->inequality && row=upper)rows) then
      invalid_arg "matching tile upper interval absent";
    let expression={ae_var_coeffs=List.init(prefix+point)(fun index->
      integer(Z.of_int(if index=prefix+prefix then 1 else 0)));
      ae_param_coeffs=List.init parameters(fun _->integer Z.zero);ae_const=integer Z.zero} in
    {tl_expr=expression;tl_tile_size=integer size}) in
  {stw_point_dim=nat point;stw_links=links}
let run_rank rank path before = try
  let input=Filename.concat path "before.scop" in
  GuardOpenScopIO.write input before;
  let binary=Option.value(Sys.getenv_opt "GUARDCERT_PLUTO")~default:"pluto" in
  let tiling=configured_mode()="tile" in
  if tiling then emit(Filename.concat path "tile.sizes")
    (String.concat "\n"(List.map string_of_int(tile_sizes rank))^"\n");
  let flags=["--readscop";"--dumpscop";"--noprevector";"--nounrolljam";
    "--noparallel";"--smartfuse"] @
    (if tiling then ["--identity";"--nointratileopt";"--nodiamond-tile";"--tile"] else ["--notile"]) in
  let arguments=Array.of_list(["/usr/bin/timeout";"60";binary] @ flags @ [input]) in
  emit(Filename.concat path "command.txt")(String.concat "\n"(Array.to_list arguments)^"\n");
  let log=Unix.openfile(Filename.concat path "scheduler.log")
    [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_EXCL]0o600 in
  let cwd=Sys.getcwd() in
  let status=Fun.protect ~finally:(fun()->Unix.chdir cwd;Unix.close log)(fun()->
    Unix.chdir path;let pid=Unix.create_process arguments.(0) arguments Unix.stdin log log in
    snd(Unix.waitpid [] pid)) in
  (match status with Unix.WEXITED 0->()|_->failwith "scheduler failed");
  let middle=GuardOpenScopIO.read before(input^".midtransform.scop") in
  let after=GuardOpenScopIO.read before(input^".afterscheduling.scop") in
  let witnesses=if tiling then List.map2(infer_ranked_witness rank)
    middle.OpenScop.statements after.OpenScop.statements else List.map(fun statement->
      {TilingWitness.stw_point_dim=statement.OpenScop.domain.meta.out_dim_nb;stw_links=[]})
      middle.OpenScop.statements in
  emit(Filename.concat path "witness.txt")(String.concat "\n"(List.map(fun witness->
    "point-dim="^string_of_int(GuardOpenScopIO.nat_to_int witness.TilingWitness.stw_point_dim)^" tile-sizes="^
    String.concat ","(List.map(fun link->integer_text link.TilingWitness.tl_tile_size)witness.TilingWitness.stw_links))witnesses)^"\n");
  Result.Okk((middle,after),witnesses)
with error ->
  let reason=match error with
    | Invalid_argument reason|Failure reason|Sys_error reason -> reason
    | Not_found -> "missing matching tile interval"
    | End_of_file -> "truncated scheduler output"
    | Unix.Unix_error(error,call,_) -> call^": "^Unix.error_message error
    | _ -> raise error in
  emit(Filename.concat path "scheduler-refusal.txt")(reason^"\n");Result.Err reason
let unit_axes_ranked rank witnesses =
  let mask witness =
    if GuardOpenScopIO.nat_to_int witness.TilingWitness.stw_point_dim<>rank ||
      List.length witness.TilingWitness.stw_links<>rank then invalid_arg "unexpected point axes";
    List.map(fun link->Z.equal(GuardMemoryNumbers.export_integer link.TilingWitness.tl_tile_size)Z.one)
      witness.TilingWitness.stw_links in
  match witnesses with
  | [] -> invalid_arg "missing tiling witness"
  | first::rest -> let units=mask first in
    if not(List.for_all(fun witness->mask witness=units)rest) then invalid_arg "inconsistent unit axes";
    units
let take count values=List.filteri(fun index _->index<count)values
let drop count values=List.filteri(fun index _->index>=count)values
let complete_ranked_units rank units code =
  let nonunit=List.filter(fun axis->not(List.nth units axis))(List.init rank Fun.id) in
  let expected_depth=rank+List.length nonunit in
  let position axis =
    let rec find index=function a::_ when a=axis->index|_::rest->find(index+1)rest|[]->assert false in
    expected_depth-1-(if List.nth units axis then axis else rank+find 0 nonunit) in
  let rec validate depth = function
    | L.Loop(_,_,body) -> validate(depth+1)body
    | L.Guard(_,body) -> validate depth body
    | L.Instr(_,arguments) ->
      let positions=List.map(function L.Var n->GuardOpenScopIO.nat_to_int n
        |_->invalid_arg "non-variable source coordinate")(take rank arguments) in
      if depth<>expected_depth || positions<>List.init rank position then
        invalid_arg "generated unit-coordinate order refused"
    | L.Seq sequence -> validate_sequence depth sequence
  and validate_sequence depth = function
    | L.SNil -> () | L.SCons(head,tail) -> validate depth head;validate_sequence depth tail in
  validate 0 code;
  let rec complete depth axis code =
    if depth>=rank && axis<rank && List.nth units axis then
      let lower=L.Var(nat(depth-1-axis)) in
      L.Loop(lower,L.Sum(lower,one),complete(depth+1)(axis+1)(lift_statement 0 code))
    else match code with
    | L.Loop(lower,upper,body) when depth<rank -> L.Loop(lower,upper,complete(depth+1)axis body)
    | L.Loop(lower,upper,body) when axis<rank -> L.Loop(lower,upper,complete(depth+1)(axis+1)body)
    | L.Guard(test,body) -> L.Guard(test,complete depth axis body)
    | L.Instr(instruction,args) when depth=2*rank && axis=rank ->
      L.Instr(instruction,List.init rank(fun axis->L.Var(nat(rank-1-axis))) @ drop rank args)
    | L.Seq sequence -> L.Seq(complete_sequence depth axis sequence)
    | _ -> invalid_arg "unsupported generated unit loop skeleton"
  and complete_sequence depth axis = function
    | L.SNil -> L.SNil
    | L.SCons(head,tail) -> L.SCons(complete depth axis head,complete_sequence depth axis tail) in
  complete 0 0 code
let reindex_ranked rank code = match first_instruction code with
  | Some(depth,args) when depth=rank ->
    let coordinates=List.map(function L.Var n->GuardOpenScopIO.nat_to_int n
      |_->invalid_arg "non-variable affine source coordinate")(take rank args) in
    if List.sort compare coordinates<>List.init rank Fun.id then None else
    let target=Array.of_list(List.map fst(List.sort(fun (_,a)(_,b)->compare b a)
      (List.mapi(fun axis v->axis,v)coordinates))) in
    let current=Array.init rank Fun.id and steps=ref [] in
    for axis=0 to rank-1 do
      let position=ref axis in
      while current.(!position)<>target.(axis) do incr position done;
      while !position>axis do
        let left= !position-1 in
        let saved=current.(left) in current.(left)<-current.(!position);current.(!position)<-saved;
        steps:=GuardMemoryAffineReindex.MemoryReindexSwap(nat left)::!steps;decr position
      done
    done;Some(List.rev !steps)
  | _ -> None
let propose rank instructions =
  let scalar_count=match instructions with
    | first::_ -> (match snd first.M.instruction_write with
      | (coefficients,_)::_ -> List.length coefficients-rank | [] -> -1)
    | [] -> -1 in
  if mode()="disabled" || rank<=0 || scalar_count<0 then None else try
    incr invocations;
    let path=Filename.concat(root())(Printf.sprintf "guardcert-phase-%d-%d"(Unix.getpid())!invocations) in
    mkdir path;
    let path=if Filename.is_relative path then Filename.concat(Sys.getcwd())path else path in
    let arrays=List.sort_uniq compare(List.concat_map(fun instruction->
      List.map fst(instruction.M.instruction_write::instruction.M.instruction_reads))instructions) in
    let maximum=List.fold_left(fun value id->Z.max value(GuardMemoryNumbers.export_positive id))Z.one arrays in
    let context=List.init(rank+scalar_count)(fun index->
      GuardMemoryNumbers.import_positive(Z.add maximum(Z.of_int(index+1)))) in
    let code=GuardMemoryScalarLoops.memory_scalar_rectangle(nat 0)(nat rank)(nat scalar_count)instructions in
    let source=((code,context),List.map(fun id->id,())(context @ arrays)) in
    emit(Filename.concat path "source.loop")(statement "" code);
    emit(Filename.concat path "source-rank.txt")(string_of_int rank^"\n");
    let model=get(P.MemoryPrepared.Extractor.extractor source) in
    let before=Option.get(P.export_memory_model model) in
    let ((middle,after),witnesses)=get(run_rank rank path before) in
    let mid=get(MP.from_openscop_like_source model middle) in
    require "affine"(force(GuardMemoryPolyhedral.GuardMemoryValidator.validate model mid));
    emit(Filename.concat path "affine-result.txt")"accepted\n";
    let tiled=get(GuardMemoryPolyhedral.GuardMemoryTilingValidator.import_canonical_tiled_after_poly mid after witnesses) in
    require "tiling"(force(GuardMemoryPolyhedral.GuardMemoryTilingValidator.checked_tiling_validate_poly mid tiled witnesses));
    emit(Filename.concat path "tiling-result.txt")"accepted\n";
    let ((items,parameters),variables)=MP.current_view_pprog tiled in
    if List.length items<>List.length instructions then invalid_arg "statement count changed";
    let generated=List.mapi(fun index item->
      let result,alarm_free=force(P.MemoryPrepared.PrepareCore.prepared_codegen(([item],parameters),variables)) in
      if not alarm_free then failwith "prepared codegen alarmed";
      let body=fst(fst result) in
      emit(Filename.concat path(Printf.sprintf "raw-statement-%d.loop"index))(statement "" body);body)items in
    let raw=L.Seq(List.fold_right(fun head tail->L.SCons(head,tail))generated L.SNil) in
    emit(Filename.concat path "raw-generated.loop")(statement "" raw);
    let has_tiles=List.exists(fun witness->witness.TilingWitness.stw_links<>[])witnesses in
    let units=if has_tiles then unit_axes_ranked rank witnesses else List.init rank(fun _->false) in
    let all_unit=has_tiles && List.for_all Fun.id units in
    let partial=has_tiles && not all_unit && List.exists Fun.id units in
    let completed=if partial then complete_ranked_units rank units raw else raw in
    emit(Filename.concat path "completed.loop")(statement "" completed);
    let candidate=adapt_bounds completed in
    emit(Filename.concat path "generated.loop")(statement "" candidate);
    let kind=if all_unit || not has_tiles then "mapped" else "tiled" in
    let proposal=if kind="mapped" then match reindex_ranked rank candidate with
      | Some steps->ClightTensorGeneratedCandidates.TensorGeneratedMapped(candidate,steps)
      | None->invalid_arg "generated affine reindex refused"
      else ClightTensorGeneratedCandidates.TensorGeneratedTiled(candidate,witnesses) in
    emit(Filename.concat path "receipt.txt")
      ("affine-validation=accepted\ntiling-validation=accepted\nprepared-codegen=successful\nprepared-codegen-scope=per-statement\nstatement-distribution=proposed\nwhole-candidate-check=pending\ncandidate-kind="^kind^"\n");
    Some proposal
  with Invalid_argument _|Failure _|Sys_error _|Stack_overflow->None
