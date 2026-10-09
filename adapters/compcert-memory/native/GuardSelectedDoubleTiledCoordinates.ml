(* Proposed coordinate completion is checked on the final actual candidate.
   Unit-tile codegen can reuse a quotient coordinate as a source point; restore
   the explicit singleton point coordinate required by the tiling witness. *)
include GuardSelectedDoubleTiledCandidate
let current_witnesses = ref []
let phase before = match GuardSelectedDoubleTiledCandidate.phase before with
  | Result.Okk((middle,after),witnesses) as result->current_witnesses:=witnesses; result
  | Result.Err _ as result->current_witnesses:=[]; result
let rec lift_expression cutoff = function
  | L.Constant _ as e -> e
  | L.Var n -> if GuardOpenScopDoubleIO.nat_to_int n >= cutoff then L.Var(Datatypes.S n) else L.Var n
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
  let dimensions=match witnesses with []->invalid_arg "missing tiling witness" | w::_->
    GuardOpenScopDoubleIO.nat_to_int w.TilingWitness.stw_point_dim in
  let mask witness =
    if GuardOpenScopDoubleIO.nat_to_int witness.TilingWitness.stw_point_dim <> dimensions ||
       List.length witness.TilingWitness.stw_links <> dimensions then
      invalid_arg "unit completion requires three point axes and tile links";
    List.map(fun link -> Z.equal(GuardMemoryNumbers.export_integer link.TilingWitness.tl_tile_size)Z.one)
      witness.TilingWitness.stw_links in
  match witnesses with
  | [] -> invalid_arg "missing tiling witness"
  | first::rest -> let units=mask first in
    if not(List.for_all(fun witness -> mask witness=units)rest) then invalid_arg "incompatible unit axes";
    units

let validate_point_slots units code =
  let dimensions=List.length units in
  let nonunit=List.filter(fun axis -> not(List.nth units axis))(List.init dimensions Fun.id) in
  let expected_depth=dimensions+List.length nonunit in
  let rank axis =
    let rec find i = function a::_ when a=axis -> i | _::rest -> find(i+1)rest | [] -> assert false in
    find 0 nonunit in
  let positions=List.init dimensions(fun axis -> expected_depth-1-
    (if List.nth units axis then axis else dimensions+rank axis)) in
  let rec check depth = function
    | L.Loop(_,_,body) -> check(depth+1)body
    | L.Guard(_,body) -> check depth body
    | L.Instr(_,args) ->
      let coordinates=List.filteri(fun index _->index<dimensions)args in
      let actual=List.map(function L.Var n->GuardOpenScopDoubleIO.nat_to_int n
        | _->invalid_arg "non-variable source coordinate")coordinates in
      if depth<>expected_depth || actual<>positions then
        invalid_arg "generated coordinate order outside unit completion"
    | L.Seq sequence -> check_sequence depth sequence
  and check_sequence depth = function
    | L.SNil -> ()
    | L.SCons(head,tail) -> check depth head;check_sequence depth tail in
  check 0 code

let complete_unit_points units code =
  let dimensions=List.length units in
  validate_point_slots units code;
  let rec complete depth axis code =
    if depth>=dimensions && axis<dimensions && List.nth units axis then
      let lo=L.Var(nat(depth-1-axis))in
      L.Loop(lo,L.Sum(lo,one),complete(depth+1)(axis+1)(lift_statement 0 code))
    else match code with
    | L.Loop(lo,hi,body) when depth<dimensions -> L.Loop(lo,hi,complete(depth+1)axis body)
    | L.Loop(lo,hi,body) when axis<dimensions -> L.Loop(lo,hi,complete(depth+1)(axis+1)body)
    | L.Guard(test,body) -> L.Guard(test,complete depth axis body)
    | L.Instr(instruction,args) when depth=2*dimensions && axis=dimensions ->
      let rest=List.filteri(fun index _->index>=dimensions)args in
      L.Instr(instruction,List.init dimensions(fun axis->L.Var(nat(dimensions-1-axis)))@rest)
    | L.Seq sequence -> L.Seq(complete_sequence depth axis sequence)
    | _ -> invalid_arg "generated loop skeleton outside unit completion"
  and complete_sequence depth axis = function
    | L.SNil -> L.SNil
    | L.SCons(head,tail) -> L.SCons(complete depth axis head,complete_sequence depth axis tail) in
  complete 0 0 code

let adapt limit ((raw,context),variables) = try
  let units=unit_axes !current_witnesses in
  let completed=if List.exists Fun.id units then complete_unit_points units raw else raw in
  (match !current_path with Some path->
    emit(Filename.concat path "original-raw-generated.loop")(statement "" raw);
    emit(Filename.concat path "completed.loop")(statement "" completed);
    emit(Filename.concat path "coordinate-completion.txt")
      ("unit-axes="^String.concat "," (List.map string_of_bool units)^"\n")
    |None->());
  GuardSelectedDoubleTiledCandidate.adapt limit ((completed,context),variables)
with (Invalid_argument _ | Failure _ | Sys_error _) as error->
  (match !current_path with Some path->emit(Filename.concat path "coordinate-refusal.txt")(Printexc.to_string error^"\n")|None->());
  Result.Err(Printexc.to_string error)
