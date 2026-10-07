(* Execute extracted syntax checks and condition construction. Actual Clight
   statement execution and memory preservation are checked by Rocq fixtures. *)
module W = ClightWordArithmeticTransport
module D = ClightDirectWordObservation
module E = ClightTensorHeaderPointExample
module F = ClightTensorHeaderFirstPoint
let p = Z.of_int
let emit name result =
  Printf.printf "{\"case\":\"%s\",\"passed\":%b}\n%!" name result;
  if not result then failwith name
let rec temps = function
  | Clight.Etempvar (id,_) -> [id]
  | Clight.Ebinop (_,a,b,_) -> temps a @ temps b
  | _ -> []
let rec tests = function
  | ClightCondition.Decision _ -> 0
  | ClightCondition.Test (_,yes,no) -> 1 + tests yes + tests no
let rec nodes = function
  | Clight.Sifthenelse (_,yes,no) | Clight.Ssequence (yes,no) -> 1 + nodes yes + nodes no
  | _ -> 1
let () =
  emit "dynamic-product" (W.word_arithmetic_check E.thp_index);
  emit "load-refused" (not (W.word_arithmetic_check E.thp_cell));
  emit "division-refused" (not (W.word_arithmetic_check
    (Clight.Ebinop (Cop.Odiv,Clight.Etempvar (p 1,Ctypes.type_int32s),
      Clight.Etempvar (p 6,Ctypes.type_int32s),Ctypes.type_int32s))));
  emit "wrong-type-refused" (not (W.word_arithmetic_check
    (Clight.Etempvar (p 6,Ctypes.Tint (Ctypes.I32,Ctypes.Unsigned,Ctypes.noattr)))));
  let replaced = W.word_replace (F.tensor_zero_binding E.thp_shape) E.thp_index in
  emit "substitution-keeps-stride" (temps replaced = [p 6] && W.word_arithmetic_check replaced);
  let tree = D.direct_word_observer_tree (F.tensor_zero_binding E.thp_shape)
    (p 10) E.thp_index (ClightNestedConstantHeaders.ncs_observer_templates E.thp_shape) in
  emit "two-observer-tests" (tests tree = 2);
  emit "actual-check-lowering" (nodes (D.direct_word_check_code (F.tensor_zero_binding E.thp_shape)
    (p 10) E.thp_index E.thp_observers (p 108)) = 5);
  emit "conditional-child-capture" (match ClightTensorHeaderCapture.tensor_header_capture E.thp_shape with
    | Clight.Ssequence (Clight.Sset (root,_),
        Clight.Sifthenelse (_,Clight.Sset (child,_),Clight.Sskip)) -> root = p 4 && child = p 5
    | _ -> false)
