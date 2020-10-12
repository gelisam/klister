#lang racket

(require racket/pretty)

; Problem: bootstrapping can be difficult. When we don't yet have convenient
; macro-defining macros like fancy-syntax-case, it can be inconvenient to write
; complex macros such as fancy-syntax-case.
;
; Solution: instead of manually defining Klister's fancy-syntax-case using
; Klister's more primitive raw-syntax-case, we write some Racket code which
; expands to the code we would have written manually. This is easier, because
; Racket does have convenient syntax-manipulating macros like match and
; quasiquote.

; (generate-define-keywords (list 'foo 'bar))
; =>
; '(define-macros
;    ([foo
;      (lambda (stx)
;        (syntax-error '"foo used out of context" stx))]
;     [bar
;      (lambda (stx)
;        (syntax-error '"bar used out of context" stx))]))
(define (generate-define-keywords keywords)
  (let* ([error-message
          (lambda (symbol)
            (string-append (symbol->string symbol)
                           " used out of context"))]
         [undefined-macro
          (lambda (keyword)
            `[,keyword
              (lambda (stx)
                (syntax-error ',(error-message keyword) stx))])]
         [undefined-macros
          (map undefined-macro keywords)])
    `(define-macros
       ,undefined-macros)))

; (generate-syntax-case 'my-macro 'stx (list 'keyword)
;   (list
;     (cons '()
;           'rhs1)
;     (cons '((,a ,b) (,c ,d))
;           'rhs2)
;     (cons '(keyword ,tail ...)
;           'rhs3)))
; =>
; '(let [failure-cc
;        (lambda ()
;          (syntax-error '"my-macro call has invalid syntax" stx))]
;    (let [failure-cc
;          (lambda ()
;            (raw-syntax-case stx
;              [(cons head tail)
;               (raw-syntax-case head
;                 [(idenx x)
;                  (>>= (free-identifier=? head 'keyword)
;                    (lambda (same-identifier)
;                      (if same-identifier
;                        rhs3
;                        (failure-cc))))]
;                 [_ (failure-cc)])]
;              [_ (failure-cc)]))]
;      (let [failure-cc
;            (lambda ()
;              (raw-syntax-case stx
;                [(cons ab cd-nil)
;                 (raw-syntax-case ab
;                   [(cons a b-nil)
;                    (...etc... rhs2)]
;                   [_ (failure-cc)])]
;                [_ (failure-cc)]))]
;        (let [failure-cc
;              (lambda ()
;                (raw-syntax-case stx
;                  [() rhs1]
;                  [_ (failure-cc)]))]
;          (failure-cc)))))
(define (generate-syntax-case macro-name stx-name keywords cases)
  (letrec ([generate-case
            (lambda (scrutinee-name case)
              (match case
                [(cons pat rhs)
                 (match pat
                   [`()
                    `(raw-syntax-case ,scrutinee-name
                       [() ,rhs]
                       [_ (failure-cc)])]
                   [`_
                    rhs]
                   [keyword
                    #:when (and (symbol? keyword)
                                (member keyword keywords))
                    (let ([ident-name (gensym 'ident)])
                      `(raw-syntax-case ,scrutinee-name
                         [(ident ,ident-name)
                          (>>= (free-identifier=? ,ident-name ',keyword)
                            (lambda (same-identifier)
                              (if same-identifier
                                ,rhs
                                (failure-cc))))]
                         [_ (failure-cc)]))]
                   [`(,'unquote ,x)
                    #:when (symbol? x)
                    `(let [,x ,scrutinee-name]
                       ,rhs)]
                   [x
                    #:when (symbol? x)
                    (raise-arguments-error
                      'generate-syntax-case
                      (string-append
                        "naked symbol "
                        (symbol->string x)
                        ": did you mean ,"
                        (symbol->string x)
                        " or to add "
                        (symbol->string x)
                        " to the list of keywords?")
                      "symbol" x
                      "keywords" keywords)]
                   [`((,'unquote ,x) ,'...)
                    `(let [,x ,scrutinee-name]
                       ,rhs)]
                   [`(,e ,'...)
                    (raise-arguments-error
                      'generate-syntax-case
                      "the syntax for ellipsis is '(,x ...)"
                      "got" `(,e ...))]
                   [`(,pat-head ,@pat-tail)
                    (let ([head-name (gensym 'head-)]
                          [tail-name (gensym 'tail-)])
                      `(raw-syntax-case ,scrutinee-name
                         [(cons ,head-name ,tail-name)
                          ,(generate-case head-name
                             (cons pat-head
                                   (generate-case tail-name
                                     (cons pat-tail rhs))))]
                         [_ (failure-cc)]))])]))]
           [generate-cases
            (lambda (cases)
              (match cases
                ['()
                 `(failure-cc)]
                [`(,@(list cases ...) ,case)
                 `(let [failure-cc
                        (lambda ()
                          ,(generate-case stx-name case))]
                    ,(generate-cases cases))]))])
    `(let [failure-cc
           (lambda ()
             (syntax-error
               ',(string-append
                   (symbol->string macro-name)
                   " call has invalid syntax")
               ,stx-name))]
       ,(generate-cases cases))))

(define (generate-define-syntax macro-name stx-name keywords cases)
  `(group
     ,(generate-define-keywords keywords)
     (define-macros
       ([,macro-name
         (lambda (,stx-name)
           ,(generate-syntax-case macro-name stx-name keywords
             cases))]))))

; `(1 ,(list 2 3) ,@(list 4 5) 6)
; =>
; '(1 (2 3) 4 5 6)
;
; (generate-quasiquote-inside
;   '(1
;     ,'(2 3)
;     ,'(4 5) ...
;     6)
;   'stx)
; =>
; '(cons-list-syntax 1
;    (cons-list-syntax '(2 3)
;      (append-list-syntax '(4 5)
;        (cons-list-syntax 6
;          '()
;          stx)
;        stx)
;      stx)
;    stx)
; =>
; (1 (2 3) 4 5 6)
(define (generate-quasiquote-inside pat stx-name)
  (match pat
    [`(,'unquote ,head)
     head]
    [`((,'unquote ,head) ,'... ,@tail)
     `(append-list-syntax
        ,head
        ,(generate-quasiquote-inside tail stx-name)
        ,stx-name)]
    [`(,head ,@tail)
     `(cons-list-syntax
        ,(generate-quasiquote-inside head stx-name)
        ,(generate-quasiquote-inside tail stx-name)
        ,stx-name)]
    [x
     `(quote ,x)]))

; (generate-quasiquote
;   '(1
;     ,'(2 3)
;     ,'(4 5) ...
;     6)
;   'stx)
; =>
; '(pair-list-syntax 'quote
;    (cons-list-syntax 1
;      ...etc...
;      stx)
;    stx)
; =>
; '(1 (2 3) 4 5 6)
(define (generate-quasiquote pat stx-name)
  `(pair-list-syntax 'quote
     ,(generate-quasiquote-inside pat stx-name)
     ,stx-name))


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
              '(import "list-syntax.kl")
              '(import (shift "list-syntax.kl" 1))
              '(import (rename (shift "prelude.kl" 1)
                               [syntax-case raw-syntax-case]))

              (generate-define-keywords (list 'fancy-unquote 'fancy-...))
              (generate-define-syntax 'fancy-quasiquote 'stx '()
                (list
                  (cons '(_ ,pat)
                        `(let [stx-name ,(generate-quasiquote
                                           ',(replace-loc pat 'here)
                                           ''here)]
                           (flet (go (pat)
                                     ,(generate-syntax-case 'fancy-quasiquote 'pat (list 'fancy-unquote 'fancy-...)
                                        (list
                                          (cons '(fancy-unquote ,x)
                                                '(pure x))
                                          (cons '((fancy-unquote ,head) fancy-... ,tail ...)
                                                `(>>= (go tail)
                                                   (lambda (inside-tail)
                                                     (pure ,(generate-quasiquote-inside
                                                              '(append-list-syntax
                                                                 ,head
                                                                 ,inside-tail
                                                                 ,stx-name)
                                                              'stx)))))
                                          (cons '(,head ,tail ...)
                                                `(>>= (go head)
                                                   (lambda (inside-head)
                                                     (>>= (go tail)
                                                       (lambda (inside-tail)
                                                         (pure ,(generate-quasiquote-inside
                                                                  '(cons-list-syntax
                                                                     ,inside-head
                                                                     ,inside-tail
                                                                     ,stx-name)
                                                                  'stx)))))))
                                          (cons ',x
                                                `(pure (pair-list-syntax
                                                          'quote
                                                          x
                                                          stx))))))
                             (>>= (go pat)
                               (lambda (inside)
                                 (pure inside))))))))
              '(example
                 (fancy-quasiquote
                   (1
                    (fancy-unquote '(2 3))
                    (fancy-unquote '(4 5)) fancy-...
                    6)))
              '(export (rename ([fancy-quasiquote quasiquote]
                                [fancy-unquote unquote]
                                [fancy-... ...])
                               fancy-quasiquote
                               fancy-unquote
                               fancy-...)))))))))