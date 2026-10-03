(each
  (loop (constant 0) (sum (var 0) (constant 1))
    (loop (constant 0) (var 2)
      (instr current ((var 1) (var 0))))))
