(map-index ((skew 1 0 1) (skew 0 1 -1) (skew 1 0 1) (swap 0))
 (loop (constant 0) (var 0)
   (loop (sum (constant 1) (scale -1 (var 2))) (constant 1)
     (each (instr current ((var 1) (scale -1 (var 0))))))))
