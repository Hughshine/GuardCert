(* Domain-only diagnostics over actual extracted candidate and imported tiled
   model. The installed compiler still uses its previous final checker. *)
include GuardSelectedDoubleTreeSpecializedCoordinates
module PF = GuardMemoryDoublePieceFamily.DoublePieceFamily
module PC = PolCertPieceCoordinates
module AF = PolCertPieceAffineMaps
module TV = GuardMemoryDoublePolyhedral.DoubleAssignmentTilingValidator
module I = GuardMemoryDoubleAssignment.DoubleAssignmentInstr

let saved_phase = ref None
let phase before =
  let answer = GuardSelectedDoubleTreeBoxPhase.phase before in
  saved_phase := (match answer with Result.Okk data -> Some data | Result.Err _ -> None);
  answer
let checked_bool operation =
  let answer = ref None in
  ImpureConfig.Core.Base.bind operation (fun (accepted,alarm_free) ->
    answer:=Some (accepted,alarm_free));
  match !answer with Some (answer,true)->answer | _->false
let pad width row =
  if List.length row>width then invalid_arg "piece row exceeds dimension";
  row @ List.init (width-List.length row) (fun _->Z.zero)
let convert (row,bias) = List.map integer row,integer bias
let unit_row width position = List.init width (fun i->if i=position then Z.one else Z.zero),Z.zero
let map_row width (row,bias) = pad width (List.map GuardMemoryNumbers.export_integer row),
  GuardMemoryNumbers.export_integer bias
let add_row (a,x) (b,y) = List.map2 Z.add a b,Z.add x y
let scale_row coefficient (a,x) = List.map (Z.mul coefficient) a,Z.mul coefficient x
let subtract_row a b = add_row a (scale_row Z.minus_one b)
let prefix_facts width intervals =
  List.concat (List.mapi (fun position (lower,upper)->
    let row,_=unit_row width position in
    [convert (row,GuardMemoryNumbers.export_integer upper);
     convert (List.map Z.neg row,Z.neg (GuardMemoryNumbers.export_integer lower))]) intervals)
let source_selectors parameters tiles source =
  let width=parameters+tiles+2 in
  let actual=List.map (map_row width) source.P.pi_transformation in
  if actual<>[unit_row width (parameters+tiles);unit_row width (parameters+tiles+1)] then
    invalid_arg "canonical source arguments are not two point coordinates"

let propose parameters intervals source candidate =
  let source_depth=IO.nat_to_int source.P.pi_depth in
  let depth=IO.nat_to_int candidate.P.pi_depth in
  let tiles=source_depth-2 in
  if tiles<0 || depth<tiles || depth>tiles+2 then invalid_arg "piece inverse shape";
  source_selectors parameters tiles source;
  let cw=parameters+depth and sw=parameters+source_depth in
  let arguments=List.map (map_row cw) candidate.P.pi_transformation in
  let x,y=match arguments with [x;y]->x,y | _->invalid_arg "piece point argument count" in
  let prefix=List.init (parameters+tiles) (unit_row cw) in
  let embed=prefix@[x;y] in
  let remove_point (row,bias) = List.mapi (fun i value->if i<parameters+tiles then value else Z.zero) row,bias in
  let transfer (row,bias) =
    List.init sw (fun i->if i<parameters+tiles then List.nth row i else Z.zero),bias in
  let x_residual=subtract_row (unit_row sw (parameters+tiles)) (transfer (remove_point x)) in
  let y_residual=subtract_row (unit_row sw (parameters+tiles+1)) (transfer (remove_point y)) in
  let project_prefix=List.init (parameters+tiles) (unit_row sw) in
  let project_points=match depth-tiles with
    | 0->[]
    | 1->
      let a=List.nth (fst x) (parameters+tiles) in
      let b=List.nth (fst y) (parameters+tiles) in
      if Z.equal (Z.abs a) Z.one then [scale_row a x_residual]
      else if Z.equal (Z.abs b) Z.one then [scale_row b y_residual]
      else invalid_arg "piece one-axis inverse is not integral"
    | 2->
      let at row offset=List.nth (fst row) (parameters+tiles+offset) in
      let a,b,c,d=at x 0,at x 1,at y 0,at y 1 in
      let determinant=Z.sub (Z.mul a d) (Z.mul b c) in
      if not (Z.equal (Z.abs determinant) Z.one) then invalid_arg "piece two-axis inverse is not unimodular";
      [scale_row determinant (subtract_row (scale_row d x_residual) (scale_row b y_residual));
       scale_row determinant (subtract_row (scale_row a y_residual) (scale_row c x_residual))]
    | _->assert false in
  {PC.piece_domain=candidate.P.pi_poly @ prefix_facts cw intervals;
   PC.piece_embed=List.map convert embed;PC.piece_project=List.map convert (project_prefix@project_points)}

let coverage source domains =
  let budget=ref 2000 in
  let include_domain source target=checked_bool (PF.D.C.memory_check_domain_inclusion source target) in
  let empty source=checked_bool (PolyTest.isBottom source) in
  let rec cover source pieces =
    decr budget; if !budget<0 then invalid_arg "piece coverage search budget";
    if empty source then PF.D.CoverEmpty else
    match List.find_opt (fun (_,domain)->include_domain source domain) pieces with
    | Some (index,_)->PF.D.CoverPiece (nat index)
    | None->match pieces with
      | []->invalid_arg "piece coverage has an uncovered path"
      | (index,domain)::rest->carve source index domain domain rest
  and carve source index domain rows rest =
    if empty source then PF.D.CoverEmpty else
    if include_domain source domain then PF.D.CoverPiece (nat index) else
    match rows with
    | []->invalid_arg "piece coverage leaf inclusion refused"
    | row::rows->
      if include_domain source [row] then carve source index domain rows rest
      else if empty (row::source) then cover source rest
      else PF.D.CoverSplit (row,carve (row::source) index domain rows rest,
        cover (Linalg.neg_constraint row::source) rest) in
  cover source (List.mapi (fun index domain->index,domain) domains)

let diagnose intervals source candidate =
  let path=match !current_path with Some path->path | None->failwith "missing piece diagnostic path" in
  let receipt=Filename.concat path "piece-family-diagnostic.txt" in
  let lines=ref ["scope=domain-coordinates-only";"whole-fusion-installed=false"] in
  let record text=lines:= !lines@[text];emit receipt (String.concat "\n" !lines ^ "\n") in
  try
    let original=match E.extractor source with Result.Okk model->model | Result.Err reason->failwith reason in
    let extracted=match E.extractor candidate with Result.Okk model->model | Result.Err reason->failwith reason in
    let (middle_scop,after_scop),witnesses=match !saved_phase with Some phase->phase | None->failwith "missing actual phase" in
    let middle=match GuardMemoryDoubleUniformPrepared.import_double_uniform_schedule original middle_scop with
      | Result.Okk model->model | Result.Err reason->failwith reason in
    let tiled=match TV.import_canonical_tiled_after_poly middle after_scop witnesses with
      | Result.Okk model->P.current_view_pprog model | Result.Err reason->failwith reason in
    let (parents,context),_=tiled in
    let (pieces,_),_=extracted in
    let parameters=List.length context in
    record (Printf.sprintf "source-instructions=%d\ncandidate-pieces=%d" (List.length parents) (List.length pieces));
    let assigned=List.mapi (fun index candidate->
      let parent=List.mapi (fun index source->index,source) parents |> List.find (fun (_,source)->I.eqb source.P.pi_instr candidate.P.pi_instr) in
      let id,source=parent in
      let proposal=propose parameters intervals source candidate in
      let width=parameters+IO.nat_to_int source.P.pi_depth in
      let source_domain=source.P.pi_poly @ prefix_facts width intervals in
      let accepted=checked_bool (PF.K.check_piece_coordinates (nat width) source_domain proposal) in
      record (Printf.sprintf "piece=%d parent=%d depth=%d coordinates=%b" index id (IO.nat_to_int candidate.P.pi_depth) accepted);
      id,proposal) pieces in
    List.iteri (fun parent source->
      let width=parameters+IO.nat_to_int source.P.pi_depth in
      let domain=source.P.pi_poly @ prefix_facts width intervals in
      let proposals=List.filter_map (fun (id,piece)->if id=parent then Some piece else None) assigned in
      let images=List.map PC.piece_image_domain proposals in
      let disjoint=checked_bool (PF.D.check_disjoint_family images) in
      record (Printf.sprintf "parent=%d pieces=%d disjoint=%b" parent (List.length proposals) disjoint);
      let witness=coverage domain images in
      let accepted=checked_bool (PF.check_piece_family (nat width) domain proposals witness) in
      record (Printf.sprintf "parent=%d checked-family=%b" parent accepted)) parents;
    record "diagnostic=completed"
  with (Invalid_argument _ | Failure _ | Not_found | Sys_error _) as error->
    record ("diagnostic=refused reason=" ^ Printexc.to_string error)

let adapt intervals source raw =
  let result=GuardSelectedDoubleTreeSpecializedCoordinates.adapt intervals source raw in
  (match result with Result.Okk candidate->diagnose intervals source candidate | Result.Err _->());
  result
