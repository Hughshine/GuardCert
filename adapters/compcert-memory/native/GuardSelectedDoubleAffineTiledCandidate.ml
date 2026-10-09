(* Untrusted affine scheduling, tiling and intra-tile scheduling proposals.
   The unchanged extracted phase and final-Loop checkers decide acceptance. *)
include GuardSelectedDoubleTiledCandidate
module Coordinates = GuardSelectedDoubleTiledCoordinates
let current_witnesses = ref []

let infer_witness before after =
  let open OpenScop in
  let open TilingWitness in
  let point = GuardOpenScopDoubleIO.nat_to_int before.domain.meta.out_dim_nb in
  let total = GuardOpenScopDoubleIO.nat_to_int after.domain.meta.out_dim_nb in
  let added = total - point in
  let params = GuardOpenScopDoubleIO.nat_to_int before.domain.meta.param_nb in
  if point <= 0 || added <= 0 ||
     GuardOpenScopDoubleIO.nat_to_int after.domain.meta.param_nb <> params then
    invalid_arg "missing tiled point space";
  let rows = List.map (fun (inequality,row) ->
    inequality,List.map GuardMemoryNumbers.export_integer row) after.domain.constrs in
  let links = List.init added (fun prefix ->
    let interval row =
      let size = Z.neg (List.nth row prefix) in
      let upper = List.map Z.neg (List.filteri (fun index _ -> index < total+params) row)
        @ [Z.sub (Z.pred size) (List.nth row (total+params))] in
      List.exists (fun (inequality,candidate) -> inequality && candidate = upper) rows in
    let lower = List.find (fun (inequality,row) ->
      inequality && List.length row = total+params+1 &&
      Z.sign (List.nth row prefix) < 0 &&
      List.for_all (fun axis -> Z.equal (List.nth row axis) Z.zero)
        (List.init (added-prefix-1) (fun index -> prefix+index+1)) &&
      List.exists (fun axis -> not (Z.equal (List.nth row (added+axis)) Z.zero))
        (List.init point Fun.id) && interval row) rows |> snd in
    let expression = {
      ae_var_coeffs = List.init prefix (fun axis -> integer (List.nth lower axis)) @
        List.init point (fun axis -> integer (List.nth lower (added+axis)));
      ae_param_coeffs = List.init params (fun index -> integer (List.nth lower (total+index)));
      ae_const = integer (List.nth lower (total+params)) } in
    {tl_expr=expression;tl_tile_size=integer (Z.neg (List.nth lower prefix))}) in
  {stw_point_dim=nat point;stw_links=links}

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
    let flags = ["--readscop";"--dumpscop";"--intratileopt";"--tile";
      "--nodiamond-tile";"--noprevector";"--nounrolljam";"--noparallel";"--smartfuse"] in
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
    let witnesses = List.map2 infer_witness middle.OpenScop.statements after.OpenScop.statements in
    let witnesses = if mode () = "wrong-witness" then
      List.map (fun witness -> {witness with TilingWitness.stw_links=[]}) witnesses else witnesses in
    let after = if mode () = "malformed" then {after with OpenScop.statements=[]} else after in
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

let canonical witness =
  let point = GuardOpenScopDoubleIO.nat_to_int witness.TilingWitness.stw_point_dim in
  List.length witness.TilingWitness.stw_links = point &&
  List.for_all (fun (prefix,link) ->
    let expression = link.TilingWitness.tl_expr in
    expression.TilingWitness.ae_var_coeffs = List.init (prefix+point)
      (fun index -> small (if index=prefix+prefix then 1 else 0)) &&
    List.for_all (fun coefficient -> Z.equal (GuardMemoryNumbers.export_integer coefficient) Z.zero)
      expression.TilingWitness.ae_param_coeffs &&
    Z.equal (GuardMemoryNumbers.export_integer expression.TilingWitness.ae_const) Z.zero)
    (List.mapi (fun prefix link -> prefix,link) witness.TilingWitness.stw_links)

let adapt limit ((raw,context),variables) = try
  let unit_links = List.exists (fun witness -> List.exists (fun link ->
    Z.equal (GuardMemoryNumbers.export_integer link.TilingWitness.tl_tile_size) Z.one)
    witness.TilingWitness.stw_links) !current_witnesses in
  let completed = if unit_links then (
    if not (List.for_all canonical !current_witnesses) then
      invalid_arg "affine unit coordinates require a new completion proposal";
    Coordinates.complete_unit_points (Coordinates.unit_axes !current_witnesses) raw
  ) else raw in
  (match !current_path with Some directory ->
    emit (Filename.concat directory "original-raw-generated.loop") (statement "" raw);
    emit (Filename.concat directory "completed.loop") (statement "" completed);
    emit (Filename.concat directory "coordinate-completion.txt")
      ("unit-links=" ^ string_of_bool unit_links ^ "\n") | None -> ());
  GuardSelectedDoubleTiledCandidate.adapt limit ((completed,context),variables)
with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
  (match !current_path with Some directory ->
    emit (Filename.concat directory "coordinate-refusal.txt") (Printexc.to_string error ^ "\n") | None -> ());
  Result.Err (Printexc.to_string error)
