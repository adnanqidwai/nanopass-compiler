(+ 3
    (let ([b 3])
        (let ([a 43])
            (+ a (let ([a 44])
                    (+ a b))))))
