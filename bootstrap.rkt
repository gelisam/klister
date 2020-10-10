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
; * In this file, we generate that Klister code using intermediate-define-syntax2.
; * intermediate-define-syntax{1,2} are defined using racket-syntax-case, and
;   expand to Klister code which uses raw-syntax-case.
;
; * In the generated Klister code, fancy-quasiquote is defined using
;   raw-syntax-case and {append,cons,pair}-list-syntax.
; * In this file, we generate that Klister code using intermediate-quasiquote2.
; * intermediate-quasiquote{1,2} are defined using racket-syntax-case.

; (intermediate-define-syntax1 my-macro (foo bar)
;   (lambda (raw-stx)
;     (pure raw-stx)))
; =>
; '(raw-define-macros
;    ([foo
;      (lambda (raw-stx)
;        (syntax-error '"foo used out of context" raw-stx))]
;     [bar
;      (lambda (raw-stx)
;        (syntax-error '"bar used out of context" raw-stx))]
;     [my-macro
;      (lambda (raw-stx)
;        (pure raw-stx))]))
(racket-define-syntax (intermediate-define-syntax1 intermediate-stx)
  (racket-syntax-case intermediate-stx ()
    [(_ macro-name (literal-id racket-...) impl)
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
             (syntax->datum #'(literal-id racket-...))]
            [undefined-macros
             (map undefined-macro symbols)])
       #`'(raw-define-macros
            (#,@undefined-macros
             [macro-name impl])))]))

; (intermediate-define-syntax2 my-macro (keyword)
;   [()
;    rhs1]
;   [((a b) (c d))
;    rhs2]
;   [(keyword tail intermediate-...)
;    rhs3])
; =>
; (intermediate-define-syntax1 my-macro (keyword)
;   (lambda (raw-stx)
;     (let [failure-cc
;           (lambda ()
;             (syntax-error '"my-macro call has invalid syntax" raw-stx))]
;       (let [failure-cc
;             (lambda ()
;               (raw-syntax-case raw-stx
;                 [(cons head tail)
;                  (>>= (free-identifier=? head 'keyword)
;                    (lambda (same-identifier)
;                      (if same-identifier
;                        rhs3
;                        (failure-cc))))]
;                 [_ (failure-cc)]))]
;         (let [failure-cc
;               (lambda ()
;                 (raw-syntax-case raw-stx
;                   [(cons ab cd-nil)
;                    (raw-syntax-case ab
;                      [(cons a b-nil)
;                       (... rhs2)]
;                      [_ (failure-cc)])]
;                   [_ (failure-cc)]))]
;           (let [failure-cc
;                 (lambda ()
;                   (raw-syntax-case raw-stx
;                     [() rhs1]
;                     [_ (failure-cc)]))]
;             (failure-cc)))))))
(racket-define-syntax (intermediate-define-syntax2 intermediate-stx)
  (racket-syntax-case intermediate-stx ()
    [(_ macro-name (intermediate-literal-id racket-...)
        cases racket-...)
     (letrec ([symbols
               (syntax->datum #'(intermediate-literal-id racket-...))]
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
                              #,(intermediate-expand-case 'raw-stx #'case))]
                        #,(intermediate-expand-cases #'(cases racket-...)))]))])
       #`(intermediate-define-syntax1 macro-name (intermediate-literal-id racket-...)
           (lambda (raw-stx)
             (let [failure-cc
                   (lambda ()
                     (syntax-error
                       '#,(string-append
                            (symbol->string (syntax->datum #'macro-name))
                            " call has invalid syntax")
                       raw-stx))]
               #,(intermediate-expand-cases #'(cases racket-...))))))]))

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
(define-syntax (intermediate-quasiquote1 intermediate-stx)
  (racket-syntax-case intermediate-stx (intermediate-unquote intermediate-...)
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
(define-syntax (intermediate-quasiquote2 intermediate-stx)
  (racket-syntax-case intermediate-stx ()
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
              '(import (rename "prelude.kl"
                               [syntax-case raw-syntax-case]))
              '(import (rename (shift "prelude.kl" 1)
                               [syntax-case raw-syntax-case]))

              '(example (cons-list-syntax '1 '(2 3 4) 'raw-stx))

              '(defun pair-list-syntax (head tail raw-stx)
                 (cons-list-syntax head
                   (cons-list-syntax tail
                     '()
                     raw-stx)
                   raw-stx))
              '(example (pair-list-syntax '1 '2 'raw-stx))

              '(defun append-list-syntax (list tail raw-stx)
                 (raw-syntax-case list
                   [()
                    tail]
                   [(cons car cdr)
                    (cons-list-syntax car
                      (append-list-syntax cdr tail raw-stx)
                      raw-stx)]))

              '(example (append-list-syntax
                          '(1 2 3)
                          '(4 5 6)
                          'raw-stx))

              `(example
                 (let [raw-stx 'raw-stx]
                   ,(intermediate-quasiquote2
                      (1
                       (intermediate-unquote '(2 3))
                       '(4 5) intermediate-...
                       6))))

              (intermediate-define-syntax2 my-macro (keyword)
                [(_ ((a b) (c d)))
                 (let [stx (cons-list-syntax a
                             (cons-list-syntax b
                               (cons-list-syntax c
                                 (cons-list-syntax d
                                   '()
                                   raw-stx)
                                 raw-stx)
                               raw-stx)
                             raw-stx)]
                   (pure (cons-list-syntax 'quote
                           (cons-list-syntax stx
                             '()
                             raw-stx)
                           raw-stx)))]
                [(_ (foo tail intermediate-...))
                 (let [stx tail]
                   (pure (cons-list-syntax 'quote
                           (cons-list-syntax stx
                             '()
                             raw-stx)
                           raw-stx)))])
              '(example (my-macro ((1 2) (3 4))))
              '(example (my-macro (keyword foo bar))))))))))
