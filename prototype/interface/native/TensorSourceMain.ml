(* This runs the extracted syntax descriptors and mathematical coordinate
   checker, then validates/lowers candidates using the recognized instruction.
   It does not execute generated Clight or implement a machine coordinate guard. *)
module D = ClightTensorSourceExample
module S = GuardMemoryTensorSource
module R = GuardMemoryTensorSourceRegion
module C = ClightTensorCandidates
module A = GuardMemoryAffineSourceExpressions

let rec n = function 0 -> Datatypes.O | amount -> Datatypes.S (n (amount-1))
let z = Z.of_int
let p = Z.of_int
let emit name expected accepted =
  Printf.printf "{\"case\":\"%s\",\"accepted\":%b}\n%!" name accepted;
  if accepted <> expected then failwith ("unexpected result: " ^ name)
let rec statement_nodes = function
  | Clight.Ssequence (a,b) | Clight.Sloop (a,b) -> 1 + statement_nodes a + statement_nodes b
  | Clight.Sifthenelse (_,a,b) -> 1 + statement_nodes a + statement_nodes b
  | _ -> 1
let candidate name expected computation =
  let outcome = ref None in
  ImpureConfig.Core.Base.bind computation (fun result -> outcome := Some result; ());
  let code,alarm_free = match !outcome with Some pair -> pair | None -> failwith "checker did not return" in
  let accepted = Option.is_some code && alarm_free in
  Printf.printf "{\"case\":\"%s\",\"accepted\":%b,\"alarm_free\":%b,\"statement_nodes\":%d}\n%!"
    name accepted alarm_free (match code with Some statement -> statement_nodes statement | None -> 0);
  if accepted <> expected then failwith ("unexpected candidate result: " ^ name)
let () =
  emit "horner-source-recognized" true (D.tensor_source_demo_recognized D.tensor_source_demo_code);
  let changed = Clight.Sassign (D.tensor_source_demo_cell,Clight.Etempvar (p 5,Ctypes.type_int32s)) in
  emit "changed-rhs" false (D.tensor_source_demo_recognized changed);
  emit "wrong-rank" false
    (D.tensor_source_demo_described [A.MemorySourceTemp (p 6);A.MemorySourceTemp (p 7)]);
  emit "unknown-coordinate" false
    (D.tensor_source_demo_described [A.MemorySourceTemp (p 6);A.MemorySourceTemp (p 7);A.MemorySourceTemp (p 99)]);
  emit "unused-read" false
    (Option.is_some (S.check_tensor_source_operation D.tensor_source_demo_dimensions D.tensor_source_demo_layout (p 9) (p 20) changed
      D.tensor_source_demo_access [D.tensor_source_demo_access] (GuardMemoryRuntime.ParameterValue (n 4))));
  emit "coordinate-box" true
    (R.tensor_source_operation_box D.tensor_source_demo_dimensions D.tensor_source_demo_layout (p 9) (p 20) D.tensor_source_demo_code
      D.tensor_source_demo_operation [n 3;n 2;n 5] [z 31;z 7] [z 3;z 31;z 5]);
  emit "wide-columns" false
    (R.tensor_source_operation_box D.tensor_source_demo_dimensions D.tensor_source_demo_layout (p 9) (p 20) D.tensor_source_demo_code
      D.tensor_source_demo_operation [n 3;n 32;n 5] [z 31;z 7] [z 3;z 31;z 5]);
  let box = [(Z.zero,z 3);(Z.zero,z 2);(Z.zero,z 5)] in
  let term coefficient offset = (List.map z coefficient,z offset) in
  emit "negative-coefficient" true
    (R.tensor_coordinate_box_check box [z 3;z 31;z 5]
      [term [-1;0;0] 2;term [0;1;0] 0;term [0;0;1] 0]);
  emit "negative-coordinate" false
    (R.tensor_coordinate_box_check box [z 3;z 31;z 5]
      [term [-1;0;0] 1;term [0;1;0] 0;term [0;0;1] 0]);
  let instructions = [S.tensor_source_instruction D.tensor_source_demo_dimensions D.tensor_source_demo_layout (p 9) (p 20)
    D.tensor_source_demo_code D.tensor_source_demo_operation] in
  let pool = [(p 101,p 102);(p 103,p 104);(p 105,p 106);(p 107,p 108);(p 109,p 110)] in
  let public = [p 6;p 7;p 8;p 88] in
  candidate "source-instruction-mapped" true
    (C.check_tensor_mapped (n 3) (z 32) (n 2) instructions D.tensor_source_demo_dimensions (p 9) (p 20)
      [p 1;p 3;p 4;p 2;p 5] public pool D.tensor_source_demo_loop []);
  candidate "source-instruction-tiled" true
    (C.check_tensor_tiled (n 3) (z 32) (n 2) instructions D.tensor_source_demo_dimensions (p 9) (p 20)
      [p 1;p 3;p 4;p 2;p 5] public pool (z 2) (z 3));
  candidate "zero-tile" false
    (C.check_tensor_tiled (n 3) (z 32) (n 2) instructions D.tensor_source_demo_dimensions (p 9) (p 20)
      [p 1;p 3;p 4;p 2;p 5] public pool Z.zero (z 3))
