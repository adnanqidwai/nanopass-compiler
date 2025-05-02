(let ([xaoxao (vector 1 42 3 53)])
  (begin
    (vector-set! xaoxao 0 21)
    (+  (vector-ref xaoxao 0) (vector-ref xaoxao 0))))