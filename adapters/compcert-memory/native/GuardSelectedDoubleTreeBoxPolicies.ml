(* Untrusted reconstruction of a mixed-depth rectangular source region. Source
   domains propose membership predicates; original typed instructions are taken
   from validated raw output. The final actual checker must accept the result. *)
include GuardSelectedDoubleTreeCommonPolicies
module IO = GuardOpenScopDoubleIO
module O = OpenScop

let parameter_expression parameters depth coefficients constant =
  let coefficients = List.mapi (fun index coefficient ->
    depth+parameters-1-index,GuardMemoryNumbers.export_integer coefficient) coefficients in
  let coefficients = List.fold_left (fun result (index,value) ->
    if Z.equal value Z.zero then result else Coefficients.add index value result)
    Coefficients.empty coefficients in
  expression (coefficients,GuardMemoryNumbers.export_integer constant)
let split count values =
  List.filteri (fun index _ -> index<count) values,
  List.filteri (fun index _ -> index>=count) values
let rectangular_box parameters domain =
  let depth = IO.nat_to_int domain.O.meta.out_dim_nb in
  if depth<1 || depth>2 || IO.nat_to_int domain.O.meta.local_dim_nb<>0 ||
     IO.nat_to_int domain.O.meta.param_nb<>parameters then invalid_arg "source box rank";
  let bounds = Array.make depth (None,None) in
  List.iter (fun (inequality,row) ->
    if not inequality || List.length row<>depth+parameters+1 then invalid_arg "source box row";
    let point,tail = split depth row in
    let params,constant = split parameters tail in
    let constant = List.hd constant in
    let nonzero = List.filter (fun (_,value) -> not (Z.equal value Z.zero))
      (List.mapi (fun axis value -> axis,GuardMemoryNumbers.export_integer value) point) in
    let parameter = parameter_expression parameters 0 params constant in
    match nonzero with
    | [axis,coefficient] when Z.equal coefficient Z.one ->
      let lower,upper = bounds.(axis) in
      if Option.is_some lower then invalid_arg "multiple source lower bounds";
      bounds.(axis) <- Some (subtract (L.Constant (integer Z.zero)) parameter),upper
    | [axis,coefficient] when Z.equal coefficient Z.minus_one ->
      let lower,upper = bounds.(axis) in
      if Option.is_some upper then invalid_arg "multiple source upper bounds";
      bounds.(axis) <- lower,Some (add parameter one)
    | _ -> invalid_arg "source box has coupled or parameter-only rows") domain.O.constrs;
  Array.to_list bounds |> List.map (function
    | Some lower,Some upper -> lower,upper
    | _ -> invalid_arg "source box is unbounded")
let source_write statement =
  let write = List.find (fun relation -> relation.O.rel_type=O.WriteTy) statement.O.access in
  let _,row = List.hd write.O.constrs in
  GuardMemoryNumbers.export_integer (List.hd (List.rev row))
let instruction_for raw identifier =
  let found = ref [] in
  let rec collect = function
    | L.Instr (instruction,_) ->
      let key = GuardMemoryNumbers.export_positive (fst instruction.M.value_instruction_write) in
      if Z.equal key identifier && not (List.mem instruction !found) then found := instruction :: !found
    | L.Loop (_,_,body) | L.Guard (_,body) -> collect body
    | L.Seq sequence -> collect_sequence sequence
  and collect_sequence = function
    | L.SNil -> ()
    | L.SCons (head,tail) -> collect head; collect_sequence tail in
  collect raw;
  match !found with [instruction] -> instruction | _ -> invalid_arg "ambiguous typed source write"
let box_membership depth box =
  let coordinate axis = L.Var (nat (depth-1-axis)) in
  List.mapi (fun axis (lower,upper) ->
    L.And (L.LE (lift_by depth lower,coordinate axis),
      L.LE (add (coordinate axis) one,lift_by depth upper))) box
  |> List.fold_left (fun rest test -> L.And (rest,test)) (L.TConstantTest true)
let mixed_box_candidate intervals raw =
  let before = match !GuardSelectedDoubleTreeBoxPhase.current_source with
    | Some before -> before | None -> invalid_arg "missing source box receipt" in
  let parameters = List.length intervals in
  let statements = List.map (fun source ->
    let box = rectangular_box parameters source.O.domain in
    let instruction = instruction_for raw (source_write source) in
    box,instruction) before.O.statements in
  let outer = fst (List.hd statements) |> List.hd in
  let depths = List.map (fun (box,_) -> List.length box) statements in
  if not (List.mem 1 depths && List.mem 2 depths) ||
    not (List.for_all (fun (box,_) -> List.hd box=outer) statements) then
    invalid_arg "not a common mixed-depth rectangular region";
  let shallow,deep = List.partition (fun (box,_) -> List.length box=1) statements in
  if statements<>shallow@deep then invalid_arg "interleaved shallow points";
  let parameter_bounds = List.map (fun (lower,upper) -> Some
    (GuardMemoryNumbers.export_integer lower,GuardMemoryNumbers.export_integer upper)) intervals in
  let lower,upper = List.fold_left (fun (lower,upper) (box,_) ->
    let lo,hi = List.nth box 1 in
    let lo = match interval parameter_bounds lo with Some (lo,_) -> lo | None -> invalid_arg "inner lower enclosure" in
    let hi = match interval parameter_bounds hi with Some (_,hi) -> hi | None -> invalid_arg "inner upper enclosure" in
    Z.min lower lo,Z.max upper hi)
    (let lo,hi=List.nth (fst (List.hd deep)) 1 in
     match interval parameter_bounds lo,interval parameter_bounds hi with
     | Some (lo,_),Some (_,hi) -> lo,hi
     | _ -> invalid_arg "inner enclosure unavailable") deep in
  let point depth (box,instruction) =
    L.Guard (box_membership depth box,L.Instr (instruction,
      List.init depth (fun axis -> L.Var (nat (depth-1-axis))))) in
  let lo,hi=outer in
  L.Loop (lo,hi,sequence (List.map (point 1) shallow @
    [L.Loop (L.Constant (integer lower),L.Constant (integer upper),sequence (List.map (point 2) deep))])),
  List.length statements

let adapt intervals ((raw,context),variables) =
  incr adaptations;
  verified_predicates := 0; cleared_floor_nodes := 0;
  try
    if List.length context<>List.length intervals then invalid_arg "source interval layout";
    let path=match !current_path with Some path->path | None->failwith "missing phase receipt" in
    emit (Filename.concat path "tree-raw-generated.loop") (statement "" raw);
    let without_singletons,singletons=singleton_eliminate raw in
    let recovered,translations=recover_points without_singletons in
    emit (Filename.concat path "tree-point-normalized.loop") (statement "" recovered);
    let proposed,reason = try
      let body,count=mixed_box_candidate intervals recovered in
      body,"mixed-box-points=" ^ string_of_int count
    with Invalid_argument _ | Not_found ->
      let body,count=coalesce_prefix recovered in
      body,"coalesced-prefixes=" ^ string_of_int count in
    emit (Filename.concat path "tree-coalesced.loop") (statement "" proposed);
    let generated,proposals=enclosing_bounds intervals proposed in
    let generated,moved=hoist_independent generated in
    emit (Filename.concat path "tree-bounded-proposals.txt") proposals;
    emit (Filename.concat path "tree-generated.loop") (statement "" generated);
    emit (Filename.concat path "tree-normalization.txt")
      (Printf.sprintf "singletons=%d translations=%d %s hoisted=%d\nfinal-check=pending\n"
        singletons translations reason moved);
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
    (match !current_path with Some path -> emit (Filename.concat path "tree-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None -> ());
    Result.Err (Printexc.to_string error)
