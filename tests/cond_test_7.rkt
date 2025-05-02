(let ([x (if 
            (let ([y (if #t #f #t)]) y)
            3
            4)])
  (+ x 3)) 
