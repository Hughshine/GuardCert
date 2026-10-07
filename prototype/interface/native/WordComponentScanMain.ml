(* These cases run extracted word evaluation and scan construction. The Rocq
   fixtures prove actual source stores and Clight scan executions. *)
module W = ClightWordArithmeticTransport
module R = ClightWordCoordinateRename
module E = ClightWordComponentScanExample
let p = Z.of_int
let emit name result =
  Printf.printf "{\"case\":\"%s\",\"passed\":%b}\n%!" name result;
  if not result then failwith name
let rec temps = function
  | Clight.Etempvar (id,_) -> [id]
  | Clight.Ebinop (_,a,b,_) -> temps a @ temps b
  | _ -> []
let rec loops = function
  | Clight.Sloop (a,b) -> 1 + loops a + loops b
  | Clight.Ssequence (a,b) | Clight.Sifthenelse (_,a,b) -> loops a + loops b
  | _ -> 0
let rec tests = function
  | Clight.Sifthenelse (_,a,b) -> 1 + tests a + tests b
  | Clight.Ssequence (a,b) | Clight.Sloop (a,b) -> tests a + tests b
  | _ -> 0
let () =
  let base = E.wcs_temps (Integers.Ptrofs.repr (p 16)) in
  let renamed = R.word_rename E.wcs_rename E.wcs_index in
  emit "runtime-product-grammar" (W.word_arithmetic_check E.wcs_index);
  emit "private-coordinate-renaming" (temps renamed = [p 1;p 6;p 103]);
  emit "runtime-stride-kept" (List.mem (p 6) (temps renamed));
  emit "exact-wrapping-five-coordinates"
    (List.for_all (fun k ->
      let current = Maps.PTree.set (p 103) (Values.Vint (Integers.Int.repr (p k))) base in
      R.word_evaluate current renamed = Some (Integers.Int.repr (p (5+k)))) [0;1;2;3;4]);
  emit "missing-coordinate-refused" (R.word_evaluate base renamed = None);
  emit "five-observation-points-accepted" (E.wcs_flag (Integers.Ptrofs.repr (p 16)));
  emit "first-header-alias-refused" (not (E.wcs_flag (Integers.Ptrofs.repr (p (-20)))));
  emit "single-cursor-loop" (loops E.wcs_scan = 1);
  emit "short-circuit-loop-tests" (tests E.wcs_scan = 4);
  emit "private-initialization" (match E.wcs_scan with
    | Clight.Ssequence (Clight.Sset (limit,_),
        Clight.Ssequence (Clight.Sset (cursor,_),Clight.Sloop _)) ->
          limit=p 104 && cursor=p 103
    | _ -> false)
