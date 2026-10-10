(* The source-aware adapter receives the actual source Loop as proposal data.
   Typed instructions and affine argument rows come from its actual extractor.
   All source/candidate obligations are still checked before installation. *)
include GuardSelectedDoubleTreeBoxPolicies
module P = GuardMemoryDoublePolyhedral.DoubleAssignmentIRs.PolyLang
module E = GuardMemoryDoublePolyhedral.DoubleAssignmentExtractor

let source_box parameters pi =
  let depth=IO.nat_to_int pi.P.pi_depth in
  let rows=P.dedup_domain_rows pi.P.pi_poly in
  rectangular_box parameters {O.rel_type=O.DomTy;
    O.meta={O.row_nb=nat (List.length rows);O.col_nb=nat (depth+parameters+2);
      O.out_dim_nb=nat depth;O.in_dim_nb=nat 0;O.local_dim_nb=nat 0;O.param_nb=nat parameters};
    O.constrs=List.map (fun row->P.listzzs_to_domain_constr row (nat parameters) (nat depth)) rows}
let original_argument parameters depth (coefficients,constant) =
  if List.length coefficients>parameters+depth then invalid_arg "source argument width";
  let coefficients=List.mapi (fun index value->
    parameters+depth-1-index,GuardMemoryNumbers.export_integer value) coefficients in
  let coefficients=List.fold_left (fun result (index,value)->
    if Z.equal value Z.zero then result else Coefficients.add index value result)
    Coefficients.empty coefficients in
  expression (coefficients,GuardMemoryNumbers.export_integer constant)
let source_membership depth box =
  let tests=List.mapi (fun axis (lower,upper)->
    let coordinate=L.Var (nat (depth-1-axis)) in
    L.And (L.LE (lift_by depth lower,coordinate),
      L.LE (add coordinate one,lift_by depth upper))) box in
  match tests with
  | []->invalid_arg "empty source point domain"
  | test::rest->List.fold_left (fun result next->L.And (result,next)) test rest

let source_mixed_candidate intervals ((source,context),variables) =
  let parameters=List.length intervals in
  let instructions=match E.extractor ((source,context),variables) with
    | Result.Okk ((instructions,_),_)->instructions
    | Result.Err reason->invalid_arg ("source extraction: " ^ reason) in
  let statements=List.map (fun pi->source_box parameters pi,pi) instructions in
  let outer=fst (List.hd statements) |> List.hd in
  let depths=List.map (fun (box,_)->List.length box) statements in
  if not (List.mem 1 depths && List.mem 2 depths) ||
    not (List.for_all (fun (box,_)->List.hd box=outer) statements) then
    invalid_arg "not a common mixed-depth rectangular region";
  let shallow,deep=List.partition (fun (box,_)->List.length box=1) statements in
  if statements<>shallow@deep then invalid_arg "interleaved shallow source points";
  let parameter_bounds=List.map (fun (lower,upper)->Some
    (GuardMemoryNumbers.export_integer lower,GuardMemoryNumbers.export_integer upper)) intervals in
  let lower,upper=List.fold_left (fun current (box,_)->
    let lo,hi=List.nth box 1 in
    match interval parameter_bounds lo,interval parameter_bounds hi with
    | Some (lo,_),Some (_,hi)->(match current with
      | None->Some (lo,hi) | Some (lower,upper)->Some (Z.min lower lo,Z.max upper hi))
    | _->invalid_arg "inner enclosure unavailable") None deep |> Option.get in
  let point depth (box,pi)=L.Guard (source_membership depth box,
    L.Instr (pi.P.pi_instr,List.map (original_argument parameters depth) pi.P.pi_transformation)) in
  let lo,hi=outer in
  L.Loop (lo,hi,sequence (List.map (point 1) shallow @
    [L.Loop (L.Constant (integer lower),L.Constant (integer upper),sequence (List.map (point 2) deep))])),
  List.length statements

let adapt intervals source ((raw,context),variables) =
  incr adaptations;
  verified_predicates:=0;cleared_floor_nodes:=0;
  try
    if List.length context<>List.length intervals then invalid_arg "source interval layout";
    let path=match !current_path with Some path->path | None->failwith "missing phase receipt" in
    emit (Filename.concat path "tree-source.loop") (statement "" (fst (fst source)));
    emit (Filename.concat path "tree-raw-generated.loop") (statement "" raw);
    let without_singletons,singletons=singleton_eliminate raw in
    let recovered,translations=recover_points without_singletons in
    emit (Filename.concat path "tree-point-normalized.loop") (statement "" recovered);
    let proposed,reason=try
      let body,count=source_mixed_candidate intervals source in
      body,"source-mixed-box-points=" ^ string_of_int count
    with Invalid_argument _ | Not_found ->
      let body,count=coalesce_prefix recovered in
      body,"coalesced-prefixes=" ^ string_of_int count in
    emit (Filename.concat path "tree-coalesced.loop") (statement "" proposed);
    let generated,proposals=enclosing_bounds intervals proposed in
    let generated,moved=hoist_independent generated in
    let extraction=match E.extractor ((generated,context),variables) with
      | Result.Okk ((instructions,_),_)->"accepted points=" ^ string_of_int (List.length instructions)
      | Result.Err reason->"refused reason=" ^ reason in
    emit (Filename.concat path "tree-candidate-extraction.txt") (extraction ^ "\n");
    emit (Filename.concat path "tree-bounded-proposals.txt") proposals;
    emit (Filename.concat path "tree-generated.loop") (statement "" generated);
    emit (Filename.concat path "tree-normalization.txt")
      (Printf.sprintf "singletons=%d translations=%d %s hoisted=%d\nfinal-check=pending\n"
        singletons translations reason moved);
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error->
    (match !current_path with Some path->emit (Filename.concat path "tree-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None->());
    Result.Err (Printexc.to_string error)
