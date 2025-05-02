(let ([a 42])
    (let ([b a])
        (let ([a 43])
            (- a (- b)))))
