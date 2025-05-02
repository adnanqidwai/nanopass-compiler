(let ([x (if 
            (let ([y (if #t #f #t)]) y)
            3
            4)])
  (+ 3 (if x 1 2))) 
