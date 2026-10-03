(map-index ((shift 0 -3))
 (loop (constant 3) (sum (var 0) (constant 3))
  (loop (constant 0) (var 2)
  (each (instr current ((sum (var 1) (scale -1 (constant 3))) (var 0)))))))
