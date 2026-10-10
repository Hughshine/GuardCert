(* Integer coverage proposals remain data. Every split and leaf is consumed
   by the existing extracted cover/piece checker before installation. *)
include GuardSelectedDoublePieceProducer
let adapt = GuardSelectedDoublePieceQuotients.adapt

let rational_row width row = map_row width row
let negate_row (coefficients,bound) = List.map Z.neg coefficients,Z.neg bound
let row_equal (a,x) (b,y) = List.length a=List.length b && List.for_all2 Z.equal a b && Z.equal x y
let difference_row multiplier (a,x) (b,y) =
  List.map2 (fun a b->Z.sub a (Z.mul multiplier b)) a b,Z.sub x (Z.mul multiplier y)
let reduce_row basis row = List.fold_left (fun ((coefficients,_) as row) (pivot,equality)->
  let factor=List.nth coefficients pivot in
  if Z.equal factor Z.zero then row else difference_row factor row equality) row basis

let equality_basis width source =
  let rows=List.map (rational_row width) source in
  List.fold_left (fun basis row->
    if not (List.exists (row_equal (negate_row row)) rows) then basis else
    let reduced=reduce_row basis row in
    let coefficients,_=reduced in
    match List.find_opt (fun (_,value)->Z.equal (Z.abs value) Z.one)
      (List.mapi (fun index value->index,value) coefficients) with
    | None->basis
    | Some (pivot,value)->
        let equality=if Z.equal value Z.one then reduced else negate_row reduced in
        basis@[pivot,equality]) [] rows

let integer_cut_rows source =
  let width=List.fold_left (fun width (coefficients,_)->max width (List.length coefficients)) 0 source in
  let basis=equality_basis width source in
  List.filter_map (fun row->
    let coefficients,bound=reduce_row basis (rational_row width row) in
    let divisor=List.fold_left (fun divisor value->Z.gcd divisor (Z.abs value)) Z.zero coefficients in
    if Z.compare divisor Z.one<=0 then None else
    let normalized=List.map (fun value->Z.divexact value divisor) coefficients,Z.ediv bound divisor in
    Some (convert normalized)) source |> List.sort_uniq compare

let coverage source domains =
  let budget=ref 2000 and integer_splits=ref 0 in
  let all_pieces=List.mapi (fun index domain->index,domain) domains in
  let include_domain source target=checked_bool (PF.D.C.memory_check_domain_inclusion source target) in
  let empty source=checked_bool (PolyTest.isBottom source) in
  let rec cover source pieces =
    decr budget; if !budget<0 then invalid_arg "integer piece coverage search budget";
    if empty source then PF.D.CoverEmpty else
    match List.find_opt (fun (_,domain)->include_domain source domain) pieces with
    | Some (index,_)->PF.D.CoverPiece (nat index)
    | None->match pieces with
      | []->strengthen source
      | (index,domain)::rest->carve source index domain domain rest
  and strengthen source =
    let cut=List.find_opt (fun row->
      not (include_domain source [row]) && empty (Linalg.neg_constraint row::source))
      (integer_cut_rows source) in
    match cut with
    | None->
        (match !current_path with None->() | Some path->
          emit (Filename.concat path "piece-uncovered-domain.json") (json_rows source ^ "\n"));
        invalid_arg "integer piece coverage has an uncovered path"
    | Some row->
        incr integer_splits;
        PF.D.CoverSplit (row,cover (row::source) all_pieces,PF.D.CoverEmpty)
  and carve source index domain rows rest =
    if empty source then PF.D.CoverEmpty else
    if include_domain source domain then PF.D.CoverPiece (nat index) else
    match rows with
    | []->invalid_arg "integer piece coverage leaf inclusion refused"
    | row::rows->
      if include_domain source [row] then carve source index domain rows rest
      else if empty (row::source) then cover source rest
      else PF.D.CoverSplit (row,carve (row::source) index domain rows rest,
        cover (Linalg.neg_constraint row::source) rest) in
  let result=cover source all_pieces in
  (match !current_path with None->() | Some path->
    let destination=Filename.concat path "piece-integer-coverage.txt" in
    let previous=if Sys.file_exists destination then
      let input=open_in destination in let data=really_input_string input (in_channel_length input) in close_in input;data else "" in
    emit destination (previous ^ Printf.sprintf "scope=untrusted-data-proposal\ninteger-splits=%d\nsearch-nodes=%d\nfinal-check=pending\n"
      !integer_splits (2000- !budget)));
  result

let propose model actual =
  try
    let (parents,context),variables=model in
    let (candidates,candidate_context),candidate_variables=actual in
    if context<>candidate_context || variables<>candidate_variables then invalid_arg "piece proposal declarations differ";
    let parameters=List.length context in
    let assignments=List.mapi (fun index candidate->
      let parent,source=List.mapi (fun index source->index,source) parents |>
        List.find (fun (_,source)->I.eqb source.P.pi_instr candidate.P.pi_instr) in
      let piece=propose parameters [] source candidate in
      (match !current_path with None->() | Some path->
        emit (Filename.concat path (Printf.sprintf "piece-proposal-%d.json" index))
          (Printf.sprintf "{\"piece\":%d,\"parent\":%d,\"source_depth\":%d,\"candidate_depth\":%d,\"source_domain\":%s,\"candidate_domain\":%s,\"embed\":%s,\"project\":%s,\"source_arguments\":%s,\"candidate_arguments\":%s,\"actual_schedule\":%s}\n"
            index parent (IO.nat_to_int source.P.pi_depth) (IO.nat_to_int candidate.P.pi_depth)
            (json_rows source.P.pi_poly) (json_rows candidate.P.pi_poly)
            (json_rows piece.PC.piece_embed) (json_rows piece.PC.piece_project)
            (json_rows source.P.pi_transformation) (json_rows candidate.P.pi_transformation)
            (json_rows candidate.P.pi_schedule)));
      parent,(candidate,piece)) candidates in
    let groups=List.mapi (fun parent _->List.filter_map
      (fun (id,item)->if id=parent then Some item else None) assignments) parents in
    if List.map fst (List.concat groups)<>candidates then invalid_arg "piece proposal static group order";
    let coverage=List.map2 (fun source group->coverage source.P.pi_poly
      (List.map (fun (_,piece)->PC.piece_image_domain piece) group) |> sequence_witness) parents groups in
    (match !current_path with None->() | Some path->
      emit (Filename.concat path "piece-proposal.txt")
        (Printf.sprintf "scope=untrusted-data-proposal\nsource-instructions=%d\ncandidate-pieces=%d\nproposal=available\n"
          (List.length parents) (List.length candidates)));
    Some (groups,coverage)
  with (Invalid_argument _ | Failure _ | Not_found | Sys_error _) as error->
    (match !current_path with None->() | Some path->
      emit (Filename.concat path "piece-proposal.txt")
        ("scope=untrusted-data-proposal\nproposal=refused reason=" ^ Printexc.to_string error ^ "\n"));
    None
