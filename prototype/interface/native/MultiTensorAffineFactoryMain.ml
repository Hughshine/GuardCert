(* Execute the extracted full producer and selected statement host.
   This does not execute the generated Clight statement or assembly. *)
module D = ClightMultiTensorDataExample
module F = ClightMultiTensorAffineFactory
module G = ClightTensorGeneratedCandidates
let rec nat = function 0 -> Datatypes.O | n -> Datatypes.S (nat (n-1))
let z = Z.of_int
let force computation =
  let result = ref None in
  ImpureConfig.Core.Base.bind computation (fun value -> result := Some value; ());
  match !result with Some value -> value | None -> failwith "no checker result"
let emit name expected accepted extras =
  Printf.printf "{\"case\":\"%s\",\"accepted\":%b%s}\n%!" name accepted extras;
  if accepted <> expected then failwith ("unexpected result: " ^ name)
let rec statement_nodes = function
  | Clight.Ssequence (a,b) | Clight.Sloop (a,b) -> 1+statement_nodes a+statement_nodes b
  | Clight.Sifthenelse (_,a,b) -> 1+statement_nodes a+statement_nodes b
  | _ -> 1
let source = D.multi_tensor_data_source
let live = ClightTempFootprint.statement_temps source @ [z 900]
let pool = List.init 71 (fun i -> z (1001+i), Ctypes.type_int32s)
let description = D.multi_tensor_data_description D.multi_tensor_data_assignments [z 42;z 45]
let checked name expected pool description propose =
  let code,alarm_free = force (F.check_multi_tensor_affine_region live pool
    (fun _ -> Some description) propose source) in
  emit name expected (alarm_free && Option.is_some code)
    (Printf.sprintf ",\"alarm_free\":%b,\"statement_nodes\":%d"
      alarm_free (match code with Some code -> statement_nodes code | None -> 0));
  code
let identity instructions = Some (G.TensorGeneratedMapped
  (GuardMemoryScalarLoops.memory_scalar_rectangle (nat 0) (nat 3) (nat 2) instructions, []))
let () =
  let target = Option.get (checked "full-producer-identity" true pool description identity) in
  ignore (checked "dependence-reversed" false pool description (fun instructions -> identity (List.rev instructions)));
  ignore (checked "missing-candidate-store" false pool description (fun instructions -> identity (List.tl instructions)));
  ignore (checked "exhausted-scan-pool" false [] description identity);
  let wrong = D.multi_tensor_data_description
    [D.multi_tensor_data_assignment (z 49) (z 51);D.multi_tensor_data_assignment (z 50) (z 49)] [z 42;z 45] in
  ignore (checked "wrong-source-description" false pool wrong identity);
  let marked = Clight.Ssequence (Clight.Slabel (z 90,source),
    Clight.Ssequence (source,Clight.Slabel (z 91,source))) in
  let transformed = ClightSelectedRegion.selected_transform_statement [z 90;z 91]
    ClightStructuredProgress.structured_progress_supported
    (GuardMemoryTiledCompiler.select_memory_tiled_table [source,target]) false marked in
  let expected = Clight.Ssequence (Clight.Slabel (z 90,target),
    Clight.Ssequence (source,Clight.Slabel (z 91,target))) in
  emit "selected-two-sites-and-unmarked" true (transformed=expected) ",\"marked_sites\":2,\"unmarked_sites\":1";
  let root = Option.get (Sys.getenv_opt "GUARDCERT_PIPELINE_DUMP") in
  List.iter (fun (mask,sizes) ->
    Unix.putenv "GUARDCERT_PIPELINE_DUMP" (Filename.concat root mask);
    Unix.putenv "GUARDCERT_TILE_SIZES" sizes;
    Unix.putenv "GUARDCERT_POLYHEDRAL_MODE" "tile";
    ignore (checked ("real-codegen-full-producer-" ^ mask) true pool description
      GuardPartitionedMultiTensorCandidate.propose))
    ["nonunit","2,3,2";"partial-unit","1,3,2";"all-unit","1,1,1"]
