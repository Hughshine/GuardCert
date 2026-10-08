(* This executable checks actual source data and real prepared-codegen proposals.
   It does not install a runtime guard or execute the generated Clight code. *)
module D = ClightMultiTensorExample
module C = ClightMultiTensorCandidates
module L = GuardMemoryLoops.L
module G = ClightTensorGeneratedCandidates
let rec nat = function 0 -> Datatypes.O | n -> Datatypes.S(nat(n-1))
let z = Z.of_int
let emit name expected accepted extras =
  Printf.printf "{\"case\":\"%s\",\"accepted\":%b%s}\n%!" name accepted extras;
  if accepted<>expected then failwith("unexpected result: "^name)
let rec statement_nodes = function
  | Clight.Ssequence(a,b) | Clight.Sloop(a,b) -> 1+statement_nodes a+statement_nodes b
  | Clight.Sifthenelse(_,a,b) -> 1+statement_nodes a+statement_nodes b
  | _ -> 1
let checked name expected instructions pointers pool proposal =
  let result=ref None in
  ImpureConfig.Core.Base.bind
    (C.check_multi_tensor_generated(nat 3)(z 32)(nat 2)instructions D.multi_tensor_demo_dimensions
      pointers D.multi_tensor_demo_layout D.multi_tensor_demo_live pool proposal)
    (fun value -> result:=Some value;());
  let code,alarm_free=match !result with Some value -> value | None -> failwith "no checker result" in
  emit name expected (alarm_free && Option.is_some code)
    (Printf.sprintf ",\"alarm_free\":%b,\"statement_nodes\":%d"
      alarm_free(match code with Some statement->statement_nodes statement|None->0))
let () =
  let body=D.multi_tensor_demo_body in
  emit "checked-two-statement-source" true(D.multi_tensor_demo_recognized body) "";
  emit "source-pointer-mismatch" false
    (D.multi_tensor_demo_recognized(Clight.Ssequence(D.multi_tensor_demo_store(z 9)(z 11),D.multi_tensor_demo_store(z 10)(z 9)))) "";
  emit "source-missing-second-store" false(D.multi_tensor_demo_recognized(D.multi_tensor_demo_store(z 9)(z 10))) "";
  let instructions=match D.multi_tensor_demo_instructions body with Some result->result|None->failwith "source checker refused" in
  if List.length instructions<>2 then failwith "two actual checked source instructions required";
  let source=D.multi_tensor_demo_source instructions in
  checked "checked-sequential-identity" true instructions D.multi_tensor_demo_pointers D.multi_tensor_demo_pool
    (G.TensorGeneratedMapped(source,[]));
  checked "dependence-reversed-two-stores" false instructions D.multi_tensor_demo_pointers D.multi_tensor_demo_pool
    (G.TensorGeneratedMapped(D.multi_tensor_demo_source(List.rev instructions),[]));
  checked "missing-candidate-store" false instructions D.multi_tensor_demo_pointers D.multi_tensor_demo_pool
    (G.TensorGeneratedMapped(D.multi_tensor_demo_source(List.tl instructions),[]));
  checked "unknown-second-pointer" false instructions [z 9] D.multi_tensor_demo_pool
    (G.TensorGeneratedMapped(source,[]));
  checked "pointer-scratch-collision" false instructions D.multi_tensor_demo_pointers
    ((z 10,z 102)::List.tl D.multi_tensor_demo_pool)(G.TensorGeneratedMapped(source,[]));
  let root=match Sys.getenv_opt "GUARDCERT_PIPELINE_DUMP" with Some value->value|None->failwith "fresh dump directory required" in
  List.iter(fun(mask,sizes) ->
    Unix.putenv "GUARDCERT_PIPELINE_DUMP"(Filename.concat root mask);
    Unix.putenv "GUARDCERT_TILE_SIZES"sizes;
    Unix.putenv "GUARDCERT_POLYHEDRAL_MODE""tile";
    let proposal=match GuardCompletedPreparedTensorCandidate.propose instructions with
      | Some value -> value | None -> emit("real-codegen-"^mask)true false ",\"proposal_returned\":false";assert false in
    checked("real-codegen-"^mask)true instructions D.multi_tensor_demo_pointers D.multi_tensor_demo_pool proposal)
    ["nonunit","2,3,2";"partial-unit","1,3,2";"all-unit","1,1,1"]
