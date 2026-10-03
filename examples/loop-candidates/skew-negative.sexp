(map-index ((skew 1 0 1))
 (loop (constant 0) (var 0)
  (loop (scale -1 (var 0)) (sum (var 2) (scale -1 (var 0)))
  (each (instr current ((var 1) (sum (var 0) (var 1))))))))
