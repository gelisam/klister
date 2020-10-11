#lang racket

(require (rename-in racket [define-syntax racket-define-syntax]
                           [syntax-case racket-syntax-case]
                           [... racket-...]))
(require racket/pretty)

; Problem: bootstrapping can be difficult. When we don't yet have convenient
; macro-defining macros like fancy-syntax-case, it can be inconvenient to write
; complex macros such as fancy-syntax-case.
;
; Solution: instead of manually defining Klister's fancy-syntax-case using
; Klister's more primitive raw-syntax-case, we write some Racket code which
; expands to the code we would have written manually. This is easier, because
; Racket does have convenient macro-defining macros like racket-syntax-case.
;
; But it's also a bit mind-bending because there are many different versions of
; syntax-case defined in terms of each other:
;
; * In the generated Klister code, fancy-syntax-case is defined using
;   raw-syntax-case and expands to code which uses raw-syntax-case.
; * In this file, we generate that Klister code using intermediate-syntax-case.
; * intermediate-syntax-case is defined using racket-syntax-case, and expands
;   to Klister code which uses raw-syntax-case.
;
; * In the generated Klister code, fancy-quasiquote is defined using
;   raw-syntax-case and {append,cons,pair}-list-syntax.
; * In this file, we generate that Klister code using intermediate-quasiquote.
; * intermediate-quasiquote is defined using racket-syntax-case.

; (intermediate-define-keywords (foo bar))
; =>
; '(raw-define-macros
;    ([foo
;      (lambda (raw-stx)
;        (syntax-error '"foo used out of context" raw-stx))]
;     [bar
;      (lambda (raw-stx)
;        (syntax-error '"bar used out of context" raw-stx))]))
(racket-define-syntax (intermediate-define-keywords racket-stx)
  (racket-syntax-case racket-stx ()
    [(_ (keyword racket-...))
     (let* ([error-message
             (lambda (symbol)
               (string-append (symbol->string symbol)
                              " used out of context"))]
            [undefined-macro
             (lambda (symbol)
               #`[#,symbol
                  (lambda (raw-stx)
                    (syntax-error '#,(error-message symbol) raw-stx))])]
            [symbols
             (syntax->datum #'(keyword racket-...))]
            [undefined-macros
             (map undefined-macro symbols)])
       #``(raw-define-macros
            (#,@undefined-macros)))]))

; (intermediate-syntax-case raw-stx (keyword)
;   [()
;    rhs1]
;   [((a b) (c d))
;    rhs2]
;   [(keyword tail intermediate-...)
;    rhs3])
; =>
; (let [failure-cc
;       (lambda ()
;         (syntax-error '"my-macro call has invalid syntax" raw-stx))]
;   (let [failure-cc
;         (lambda ()
;           (raw-syntax-case raw-stx
;             [(cons head tail)
;              (>>= (free-identifier=? head 'keyword)
;                (lambda (same-identifier)
;                  (if same-identifier
;                    rhs3
;                    (failure-cc))))]
;             [_ (failure-cc)]))]
;     (let [failure-cc
;           (lambda ()
;             (raw-syntax-case raw-stx
;               [(cons ab cd-nil)
;                (raw-syntax-case ab
;                  [(cons a b-nil)
;                   (... rhs2)]
;                  [_ (failure-cc)])]
;               [_ (failure-cc)]))]
;       (let [failure-cc
;             (lambda ()
;               (raw-syntax-case raw-stx
;                 [() rhs1]
;                 [_ (failure-cc)]))]
;         (failure-cc)))))
(racket-define-syntax (intermediate-syntax-case racket-stx)
  (racket-syntax-case racket-stx ()
    [(_ intermediate-stx (keyword racket-...)
        cases racket-...)
     (letrec ([symbols
               (syntax->datum #'(keyword racket-...))]
              [intermediate-expand-case
               (lambda (scrutinee-name intermediate-case-stx)
                 (racket-syntax-case intermediate-case-stx (intermediate-...)
                   [[() rhs]
                    #`(raw-syntax-case #,scrutinee-name
                        [() rhs]
                        [_ (failure-cc)])]
                   [[x rhs]
                    (and (identifier? #'x)
                         (member (syntax->datum #'x) symbols))
                    #`(>>= (free-identifier=? #,scrutinee-name 'x)
                        (lambda (same-identifier)
                          (if same-identifier rhs (failure-cc))))]
                   [[x rhs]
                    (identifier? #'x)
                    #`(let [x #,scrutinee-name]
                        rhs)]
                   [[(x intermediate-...) rhs]
                    #`(let [x #,scrutinee-name]
                        rhs)]
                   [[(intermediate-head intermediate-tail racket-...) rhs]
                    (let ([head-name (gensym 'head-)]
                          [tail-name (gensym 'tail-)])
                      #`(raw-syntax-case #,scrutinee-name
                          [(cons #,head-name #,tail-name)
                           #,(intermediate-expand-case head-name
                               #`[intermediate-head
                                  #,(intermediate-expand-case tail-name
                                      #`[(intermediate-tail racket-...) rhs])])]
                          [_ (failure-cc)]))]))]
              [intermediate-expand-cases
               (lambda (intermediate-cases-stx)
                 (racket-syntax-case intermediate-cases-stx (intermediate-...)
                   [()
                    #`(failure-cc)]
                   [(cases racket-... case)
                    #`(let [failure-cc
                            (lambda ()
                              #,(intermediate-expand-case #'intermediate-stx #'case))]
                        #,(intermediate-expand-cases #'(cases racket-...)))]))])
       #``(let [failure-cc
                (lambda ()
                  (syntax-error
                    '#,(string-append
                         (symbol->string (syntax->datum #'macro-name))
                         " call has invalid syntax")
                    intermediate-stx))]
            #,(intermediate-expand-cases #'(cases racket-...))))]))

(define-syntax (intermediate-define-syntax2 intermediate-stx)
  (syntax-case intermediate-stx ()
    [(_ macro-name (keyword racket-...)
        case racket-...)
     #'`(group
          ,(intermediate-define-keywords (keyword racket-...))
          (define-macros
            ([macro-name
              (lambda (raw-stx)
                ,(intermediate-syntax-case raw-stx (keyword racket-...)
                  case racket-...))])))]))

; `(1 ,(list 2 3) ,@(list 4 5) 6)
; =>
; '(1 (2 3) 4 5 6)
;
; (intermediate-quasiquote1
;   (1
;    (intermediate-unquote '(2 3))
;    '(4 5) intermediate-...
;    6))
; =>
; '(cons-list-syntax 1
;    (cons-list-syntax '(2 3)
;      (append-list-syntax '(4 5)
;        (cons-list-syntax 6
;          '()
;          raw-stx)
;        raw-stx)
;      raw-stx)
;    raw-stx)
; =>
; (1 (2 3) 4 5 6)
(define-syntax (intermediate-quasiquote1 racket-stx)
  (racket-syntax-case racket-stx (intermediate-unquote intermediate-...)
    [(_ ((intermediate-unquote head) tail racket-...))
     #'`(cons-list-syntax
          head
          ,(intermediate-quasiquote1 (tail racket-...))
          raw-stx)]
    [(_ (head intermediate-... tail racket-...))
     #'`(append-list-syntax
          head
          ,(intermediate-quasiquote1 (tail racket-...))
          raw-stx)]
    [(_ (head tail racket-...))
     #'`(cons-list-syntax
          ,(intermediate-quasiquote1 head)
          ,(intermediate-quasiquote1 (tail racket-...))
          raw-stx)]
    [(_ x)
     #'''x]))

; (intermediate-quasiquote2
;   (1
;    (intermediate-unquote '(2 3))
;    '(4 5) intermediate-...
;    6))
; =>
; ...
; =>
; '(1 (2 3) 4 5 6)
(define-syntax (intermediate-quasiquote2 racket-stx)
  (racket-syntax-case racket-stx ()
    [(_ e)
     #'`(pair-list-syntax 'quote
          ,(intermediate-quasiquote1 e)
          raw-stx)]))


(void
  (call-with-output-file
    "examples/dot-dot-dot.kl"
    #:exists 'truncate
    (lambda (out)
      (parameterize ([current-output-port out]
                     [pretty-print-columns 40])
        (let ([newline
                (lambda ()
                  (pretty-print-newline out (pretty-print-columns)))]
              [displayln
                (lambda (s)
                  (pretty-display s #:newline? #t))]
              [writeln
                (lambda (v)
                  (pretty-write v #:newline? #t))])
          (displayln "#lang \"prelude.kl\"")
          (displayln "-- GENERATED BY ../bootstrap.rkt, DO NOT EDIT")

          (map
            (lambda (form)
              (newline)
              (writeln form))
            (list
              '(import (rename "prelude.kl"
                               [define-macros raw-define-macros]))
              '(import (shift "list-syntax.kl" 1))
              '(import (rename (shift "prelude.kl" 1)
                               [syntax-case raw-syntax-case]))

              (intermediate-define-syntax2 my-macro (keyword)
                [(_ ((a b) (c d)))
                 (pure ,(intermediate-quasiquote2 (a b c d)))]
                [(_ (foo tail intermediate-...))
                 (pure (pair-list-syntax 'quote tail raw-stx))])
              '(example (my-macro ((1 2) (3 4))))
              '(example (my-macro (keyword foo bar))))))))))
