(map-index ((shift 0 -5) (swap 0))
 (loop (constant 5) (sum (var 1) (constant 5))
  (loop (constant 0) (var 1)
  (each (instr current ((var 0) (sum (var 1) (scale -1 (constant 5)))))))))
