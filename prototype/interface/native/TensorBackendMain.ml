(* This harness exercises the extracted candidate checker and lowerer. It does
   not claim a C frontend correspondence or execute the generated statements. *)
module D = ClightTensorBackendExample
module C = ClightTensorCandidates
module B = GuardMemoryDynamicTensorBackend

let rec natural = function 0 -> Datatypes.O | n -> Datatypes.S (natural (n-1))
let n = natural
let z = Z.of_int
let p = Z.of_int
let instructions = [D.tensor_demo_rmw]
let pool = D.tensor_demo_pool @ [(p 107,p 108);(p 109,p 110)]

let rec statement_nodes = function
  | Clight.Ssequence (a,b) | Clight.Sloop (a,b) -> 1 + statement_nodes a + statement_nodes b
  | Clight.Sifthenelse (_,a,b) -> 1 + statement_nodes a + statement_nodes b
  | _ -> 1

let check_case name expected computation =
  let outcome = ref None in
  ImpureConfig.Core.Base.bind computation (fun result -> outcome := Some result; ());
  let code,alarm_free = match !outcome with Some pair -> pair | None -> failwith "checker did not return" in
  let accepted = Option.is_some code && alarm_free in
  Printf.printf "{\"case\":\"%s\",\"accepted\":%b,\"alarm_free\":%b,\"statement_nodes\":%d}\n%!"
    name accepted alarm_free (match code with Some statement -> statement_nodes statement | None -> 0);
  if accepted <> expected then failwith ("unexpected checker result: " ^ name)

let () =
  check_case "identity-vector-rmw" true
    (C.check_tensor_mapped (n 3) (z 32) (n 2) instructions D.tensor_demo_dimensions (p 9) (p 20)
      D.tensor_demo_layout [] pool D.tensor_demo_source_loop []);
  check_case "tile-2-3-vector-rmw" true
    (C.check_tensor_tiled (n 3) (z 32) (n 2) instructions D.tensor_demo_dimensions (p 9) (p 20)
      D.tensor_demo_layout [] pool (z 2) (z 3));
  check_case "zero-tile" false
    (C.check_tensor_tiled (n 3) (z 32) (n 2) instructions D.tensor_demo_dimensions (p 9) (p 20)
      D.tensor_demo_layout [] pool Z.zero (z 3));
  check_case "layout-scratch-collision" false
    (C.check_tensor_mapped (n 3) (z 32) (n 2) instructions D.tensor_demo_dimensions (p 9) (p 20)
      D.tensor_demo_layout [] ((p 2,p 102)::List.tl pool) D.tensor_demo_source_loop []);
  check_case "wrong-scalar-arity" false
    (C.check_tensor_tiled (n 3) (z 32) (n 2) instructions D.tensor_demo_dimensions (p 9) (p 20)
      (List.tl D.tensor_demo_layout) [] pool (z 2) (z 3));
  let observed = ClightTensorBackendGuard.tensor_observe_dimensions D.tensor_demo_dimensions D.tensor_demo_temps in
  let volume_ok = match observed with Some dimensions ->
      ClightTensorVolumeGuard.tensor_volume_check GuardMemoryDynamicTensorLayout.tensor_volume_cap Z.one dimensions
    | None -> false in
  Printf.printf "{\"case\":\"observed-runtime-layout\",\"accepted\":%b}\n%!" volume_ok;
  if not volume_ok then failwith "observed layout";
  let overflow = ClightTensorVolumeGuard.tensor_volume_check GuardMemoryDynamicTensorLayout.tensor_volume_cap Z.one
    [z 46341;z 46341;Z.one] in
  Printf.printf "{\"case\":\"volume-overflow\",\"accepted\":%b}\n%!" overflow;
  if overflow then failwith "overflow accepted"
