(* Untrusted phase data can contain tiled and untiled statements.
   Zero links denote the identity point embedding, not an identity schedule.
   Both schedule checks and the final actual-body check remain authoritative. *)
include GuardSelectedDoubleAffineTiledCandidate

let infer_witness before after =
  let point = GuardOpenScopDoubleIO.nat_to_int before.OpenScop.domain.meta.out_dim_nb in
  let total = GuardOpenScopDoubleIO.nat_to_int after.OpenScop.domain.meta.out_dim_nb in
  let parameters = GuardOpenScopDoubleIO.nat_to_int before.OpenScop.domain.meta.param_nb in
  if point <= 0 || total < point ||
    GuardOpenScopDoubleIO.nat_to_int after.OpenScop.domain.meta.param_nb <> parameters then
    invalid_arg "phase point dimensions or parameter layout differ";
  if total = point then {TilingWitness.stw_point_dim=nat point;stw_links=[]}
  else GuardSelectedDoubleAffineTiledCandidate.infer_witness before after

(* Remove zero schedule components only after reconstructing every output
   equation. Pluto may erase source tree zeros while preserving the same order. *)
let schedule_signature relation =
  let outputs = GuardOpenScopDoubleIO.nat_to_int relation.OpenScop.meta.out_dim_nb in
  let rows = List.map (fun (inequality,row) ->
    inequality,List.map GuardMemoryNumbers.export_integer row) relation.OpenScop.constrs in
  let output axis =
    match List.find_opt (fun (inequality,row) -> not inequality &&
      List.length row >= outputs && Z.equal (Z.abs (List.nth row axis)) Z.one &&
      List.for_all (fun other -> other=axis || Z.equal (List.nth row other) Z.zero)
        (List.init outputs Fun.id)) rows with
    | None -> None
    | Some (_,row) ->
      let factor = Z.neg (List.nth row axis) in
      Some (List.filteri (fun column _ -> column >= outputs) row |> List.map (Z.mul factor)) in
  let expressions = List.init outputs output in
  if List.exists Option.is_none expressions then None else
  Some (List.filter (fun row -> not (List.for_all (Z.equal Z.zero) row))
    (List.map Option.get expressions))

let same_schedule before after =
  List.length before.OpenScop.statements = List.length after.OpenScop.statements &&
  List.for_all2 (fun a b ->
    match schedule_signature a.OpenScop.scattering,schedule_signature b.OpenScop.scattering with
    | Some a,Some b -> a=b
    | _ -> a.OpenScop.scattering=b.OpenScop.scattering)
    before.OpenScop.statements after.OpenScop.statements

let permute_schedule order source =
  let statements = List.map (fun statement ->
    let point = GuardOpenScopDoubleIO.nat_to_int statement.OpenScop.domain.meta.out_dim_nb in
    if List.sort compare order <> List.init point Fun.id then
      invalid_arg "manual affine order must permute each statement's point axes";
    let relation = statement.OpenScop.scattering in
    let outputs = GuardOpenScopDoubleIO.nat_to_int relation.OpenScop.meta.out_dim_nb in
    if GuardOpenScopDoubleIO.nat_to_int relation.OpenScop.meta.in_dim_nb <> point then
      invalid_arg "manual affine order requires source input axes";
    let inverse axis =
      let rec find position = function
        | value::_ when value=axis -> position
        | _::rest -> find (position+1) rest
        | [] -> assert false in
      find 0 order in
    let constrs = List.map (fun (inequality,row) -> inequality,
      List.mapi (fun column value ->
        if column>=outputs && column<outputs+point then
          List.nth row (outputs+inverse (column-outputs)) else value) row)
      relation.OpenScop.constrs in
    {statement with OpenScop.scattering={relation with OpenScop.constrs=constrs}})
    source.OpenScop.statements in
  {source with OpenScop.statements=statements}

let phase before = if not (enabled ()) then Result.Err "affine tiling disabled" else
  let path = ref None in
  current_witnesses := [];
  try
    incr calls;
    Printf.eprintf "GUARDCERT_DOUBLE_TILING_PIPELINE call=%d mode=%s affine=true intratile=true\n%!"
      !calls (mode ());
    let directory = Filename.concat (Sys.getenv "GUARDCERT_ORIGINAL_OUTPUT")
      (Printf.sprintf "tiling-pipeline-%d" !calls) in
    Unix.mkdir directory 0o700; path := Some directory; current_path := Some directory;
    let input = Filename.concat directory "before.scop" in
    GuardOpenScopDoubleIO.write input before;
    if mode () = "refuse" then failwith "requested external affine tiling refusal";
    let dimensions = List.fold_left (fun count statement -> max count
      (GuardOpenScopDoubleIO.nat_to_int statement.OpenScop.domain.meta.out_dim_nb))
      0 before.OpenScop.statements in
    emit (Filename.concat directory "tile.sizes")
      (String.concat "\n" (List.map string_of_int (sizes dimensions)) ^ "\n");
    let tile = Sys.getenv_opt "GUARDCERT_PHASE_KIND" <> Some "untiled" in
    let flags = ["--readscop";"--dumpscop";"--intratileopt"] @
      (if tile then ["--tile"] else []) @
      ["--nodiamond-tile";"--noprevector";"--nounrolljam";"--noparallel";"--smartfuse"] in
    let middle,after = match Sys.getenv_opt "GUARDCERT_PHASE_ORDER" with
    | Some order ->
      let order = List.map int_of_string (String.split_on_char ',' order) in
      let middle = permute_schedule order before in
      emit (Filename.concat directory "command.txt") "manual-affine-order-proposal\n";
      emit (Filename.concat directory "scheduler.log")
        ("manual-affine-order=" ^ String.concat "," (List.map string_of_int order) ^ "\n");
      GuardOpenScopDoubleIO.write (input ^ ".midtransform.scop") middle;
      GuardOpenScopDoubleIO.write (input ^ ".afterscheduling.scop") middle;
      middle,middle
    | None ->
    let command = "/usr/bin/timeout" in
    let arguments = Array.of_list (command :: "60" :: Sys.getenv "GUARDCERT_PLUTO" :: flags @ [input]) in
    emit (Filename.concat directory "command.txt") (String.concat "\n" (Array.to_list arguments) ^ "\n");
    let log = Unix.openfile (Filename.concat directory "scheduler.log")
      [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_EXCL] 0o600 in
    let cwd = Sys.getcwd () in
    let status = Fun.protect ~finally:(fun () -> Unix.chdir cwd; Unix.close log) (fun () ->
      Unix.chdir directory;
      let pid = Unix.create_process command arguments Unix.stdin log log in
      snd (Unix.waitpid [] pid)) in
    (match status with Unix.WEXITED 0 -> () | _ -> failwith "Pluto affine tiling failed");
    let middle = GuardOpenScopDoubleIO.read before (input ^ ".midtransform.scop") in
    let after = GuardOpenScopDoubleIO.read before (input ^ ".afterscheduling.scop") in
    middle,after in
    let witnesses = List.map2 infer_witness middle.OpenScop.statements after.OpenScop.statements in
    let witnesses = if mode () = "wrong-witness" then
      List.map (fun witness -> if witness.TilingWitness.stw_links=[] then
        {witness with TilingWitness.stw_point_dim=Datatypes.S witness.TilingWitness.stw_point_dim}
        else {witness with TilingWitness.stw_links=[]}) witnesses else witnesses in
    let after = if mode () = "malformed" then {after with OpenScop.statements=[]} else after in
    let added = List.map (fun witness -> List.length witness.TilingWitness.stw_links) witnesses in
    let unchanged = List.for_all ((=) 0) added &&
      same_schedule before middle && same_schedule middle after in
    emit (Filename.concat directory "phase-shape.txt")
      ("added-dimensions=" ^ String.concat "," (List.map string_of_int added) ^
       "\nschedule-unchanged=" ^ string_of_bool unchanged ^ "\n");
    Printf.eprintf "GUARDCERT_DOUBLE_PHASE_SHAPE added=%s unchanged=%b\n%!"
      (String.concat "," (List.map string_of_int added)) unchanged;
    if unchanged then failwith "scheduler returned an unchanged untiled schedule";
    current_witnesses := witnesses;
    let show_link link =
      let expression = link.TilingWitness.tl_expr in
      "size=" ^ integer_text link.TilingWitness.tl_tile_size ^
      " vars=" ^ String.concat "," (List.map integer_text expression.TilingWitness.ae_var_coeffs) ^
      " params=" ^ String.concat "," (List.map integer_text expression.TilingWitness.ae_param_coeffs) ^
      " const=" ^ integer_text expression.TilingWitness.ae_const in
    emit (Filename.concat directory "witness.txt") (String.concat "\n" (List.map (fun witness ->
      "point-dim=" ^ string_of_int (GuardOpenScopDoubleIO.nat_to_int witness.TilingWitness.stw_point_dim) ^
      "\n" ^ String.concat "\n" (List.map show_link witness.TilingWitness.stw_links)) witnesses) ^ "\n");
    Result.Okk ((middle,after),witnesses)
  with (Invalid_argument _ | Failure _ | Sys_error _ | Not_found | End_of_file | Unix.Unix_error _) as error ->
    let reason = Printexc.to_string error in
    current_witnesses := [];
    (match !path with Some directory -> emit (Filename.concat directory "refusal.txt") (reason ^ "\n") | None -> ());
    Printf.eprintf "GUARDCERT_DOUBLE_TILING_REFUSED reason=%S\n%!" reason;
    Result.Err reason

