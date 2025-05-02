#lang racket


(define emp null)
(define (create-conclude-block-label name)
  (string->symbol (string-append (symbol->string name) "conclusion")))

(create-conclude-block-label '())