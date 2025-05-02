(let ([a 42])
    (let ([b a])
        (let ([a 43])
            (+ a (let ([a (let ([a 44]) a)]) a)))))
                    
