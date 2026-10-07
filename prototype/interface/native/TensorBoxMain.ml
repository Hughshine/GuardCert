(* Run the extracted condition synthesizer/lowerer and its mathematical flag.
   Generated Clight expression execution is covered by Rocq decision_run
   theorems; this executable does not interpret or execute that Clight. *)
module D = ClightTensorBoxExample
module B = ClightTensorBoxGuard
module S = ClightTensorSourceExample

let z = Z.of_int
let emit name expected accepted =
  Printf.printf "{\"case\":\"%s\",\"accepted\":%b}\n%!" name accepted;
  if accepted <> expected then failwith ("unexpected result: " ^ name)
let rec tree_tests = function
  | ClightCondition.Decision _ -> 0
  | ClightCondition.Test (_,yes,no) -> 1 + tree_tests yes + tree_tests no
let compiled name expected result =
  let accepted = Option.is_some result in
  let tests = match result with Some tree -> tree_tests tree | None -> 0 in
  Printf.printf "{\"case\":\"%s\",\"accepted\":%b,\"generated_tests\":%d}\n%!" name accepted tests;
  if accepted <> expected then failwith ("unexpected compilation: " ^ name)
let term coefficients offset = List.map z coefficients,z offset
let coordinates coefficient offset =
  [[term [coefficient;0;0;0;0] offset;
    term [0;1;0;0;0] 0; term [0;0;1;0;0] 0]]
let flag accesses columns components stride alpha =
  D.tensor_box_demo_semantic_flag accesses (z columns) (z components) (z stride) alpha
let () =
  compiled "coordinate-guard-compiled" true
    (D.tensor_box_demo_compile D.tensor_box_demo_accesses);
  compiled "negative-coefficient-compiled" true (D.tensor_box_demo_compile (coordinates (-1) 2));
  compiled "intermediate-overflow" false (D.tensor_box_demo_compile (coordinates 2147483647 0));
  compiled "unknown-dimension" false
    (B.compile_tensor_box_guard D.tensor_box_demo_layout D.tensor_box_demo_profile
      [z 1;z 3;z 4] D.tensor_box_demo_scalars
      [GuardMemoryDynamicTensorBackend.TensorDimensionTemp (z 99)] D.tensor_box_demo_accesses);
  compiled "profile-arity" false
    (B.compile_tensor_box_guard D.tensor_box_demo_layout []
      [z 1;z 3;z 4] D.tensor_box_demo_scalars S.tensor_source_demo_dimensions D.tensor_box_demo_accesses);
  emit "coordinate-box" true (flag D.tensor_box_demo_accesses 2 5 31 (z 7));
  emit "wide-columns" false (flag D.tensor_box_demo_accesses 32 5 31 (z 7));
  emit "wide-components" false (flag D.tensor_box_demo_accesses 2 6 31 (z 7));
  emit "outside-runtime-profile" false (flag D.tensor_box_demo_accesses 2 5 1001 (z 7));
  emit "negative-coefficient" true (flag (coordinates (-1) 2) 2 5 31 (z 7));
  emit "negative-coordinate" false (flag (coordinates (-1) 1) 2 5 31 (z 7));
  emit "maximum-signed-scalar" true
    (flag D.tensor_box_demo_accesses 2 5 31 (Z.of_string "2147483647"));
  emit "minimum-signed-scalar" true
    (flag D.tensor_box_demo_accesses 2 5 31 (Z.of_string "-2147483648"))
