#lang racket

(define (f a [b "main"])
    (string-append a b))

(f "hi")