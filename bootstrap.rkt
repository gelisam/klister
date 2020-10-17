#lang racket

(require (rename-in racket [syntax-case racket-syntax-case]))
(require racket/pretty)

; Problem: bootstrapping can be difficult. When we don't yet have convenient
; macro-defining macros like fancy-syntax-case, it can be inconvenient to write
; complex macros such as fancy-syntax-case.
;
; Solution: instead of manually defining Klister's fancy-syntax-case using
; Klister's more primitive raw-syntax-case, we write some Racket code which
; expands to the code we would have written manually. This is easier, because
; Racket does have convenient syntax-manipulating macros like match,
; quasiquote, and racket-syntax-case.

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
;     (list '()
;           'rhs1)
;     (list '((,a ,b) (,c ,d))
;           'rhs2)
;     (list '(keyword ,tail ...)
;           '(> (length tail) 2)
;           'rhs3)))
; =>
; '(let [failure-cc
;        (lambda ()
;          (syntax-error '"my-macro call has invalid syntax" stx))]
;    (let [failure-cc
;          (lambda ()
;            (raw-syntax-case stx
;              [(cons head tail)
;               (if (identifier? head)
;                   (>>= (free-identifier=? head 'keyword)
;                     (lambda (same-identifier)
;                       (if same-identifier
;                         (if (> (length tail) 2)
;                             rhs3
;                             (failure-cc))
;                         (failure-cc))))
;                   (failure-cc))]
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
(define (generate-syntax-case macro-name stx-expr keywords cases)
  (letrec ([stx-name (gensym 'stx-)]
           [failure-cc-name (gensym 'failure-cc-)]
           [generate-guard-rhs
            (lambda (guard-rhs)
              (match guard-rhs
                [`(,guard ,rhs)
                 `(>>= ,guard
                    (lambda (guard-approves)
                      (if guard-approves ,rhs (,failure-cc-name))))]
                [`(,rhs)
                 rhs]))]
           [generate-case
            (lambda (scrutinee-name case)
              (match case
                [(cons pat guard-rhs)
                 (match pat
                   [`()
                    `(raw-syntax-case ,scrutinee-name
                       [() ,(generate-guard-rhs guard-rhs)]
                       [_ (,failure-cc-name)])]
                   [`_
                    (generate-guard-rhs guard-rhs)]
                   [keyword
                    #:when (and (symbol? keyword)
                                (member keyword keywords))
                    `(if (identifier? ,scrutinee-name)
                         (>>= (free-identifier=? ,scrutinee-name ',keyword)
                              (lambda (same-identifier)
                                (if same-identifier
                                    ,(generate-guard-rhs guard-rhs)
                                    (,failure-cc-name))))
                         (,failure-cc-name))]
                   [`(,'unquote ,x)
                    #:when (symbol? x)
                    `(let [,x ,scrutinee-name]
                       ,(generate-guard-rhs guard-rhs))]
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
                       ,(generate-guard-rhs guard-rhs))]
                   [`(,e ,'...)
                    (raise-arguments-error
                      'generate-syntax-case
                      "the syntax for ellipsis is '(,x ...)"
                      "found" `(,e ...))]
                   [`(,pat-head ,@pat-tail)
                    (let ([head-name (gensym 'head-)]
                          [tail-name (gensym 'tail-)])
                      `(raw-syntax-case ,scrutinee-name
                         [(cons ,head-name ,tail-name)
                          ,(generate-case head-name
                             (list pat-head
                                   (generate-case tail-name
                                     (cons pat-tail guard-rhs))))]
                         [_ (,failure-cc-name)]))])]))]
           [generate-cases
            (lambda (cases inner)
              (match cases
                ['()
                 inner]
                [`(,case ,@cases)
                 (generate-cases cases
                   `(let [,failure-cc-name
                          (lambda ()
                            ,(generate-case stx-name case))]
                      ,inner))]))])
    `(let [,stx-name ,stx-expr]
       (let [,failure-cc-name
             (lambda ()
               (syntax-error
                 ',(string-append
                     (symbol->string macro-name)
                     " call has invalid syntax")
                 ,stx-name))]
         ,(generate-cases cases `(,failure-cc-name))))))

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
; (generate-quasiquote
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
; '(1 (2 3) 4 5 6)
(define (generate-quasiquote pat stx-name)
  (match pat
    [`(,'unquote ,x)
     x]
    [`((,'unquote ,head) ,'... ,@tail)
     `(append-list-syntax
        ,head
        ,(generate-quasiquote tail stx-name)
        ,stx-name)]
    [`(,head ,@tail)
     `(cons-list-syntax
        ,(generate-quasiquote head stx-name)
        ,(generate-quasiquote tail stx-name)
        ,stx-name)]
    [x
     `(quote ,x)]))


; (auto-splice
;   (define-macros
;     ([my-macro
;       (lambda (stx)
;         (generate-syntax-case my-macro stx (keyword)
;           [()
;            (pure ''nil)]
;           [((,a ,b) (,c ,d))
;            (let [quadruple (generate-quasiquote (,a ,b ,c ,d) stx)]
;              (pure (generate-quasiquote '(four-elements ,quadruple) stx)))]
;           [(keyword ,tail ...)
;            (pure (generate-quasiquote '(keyword-prefixed (,tail ...)) stx))]))])))
; =>
; `(define-macros
;    ([my-macro
;      (lambda (stx)
;        ,(generate-syntax-case 'my-macro 'stx (list 'keyword)
;          (list
;            (list '()
;                  `(pure ''nil))
;            (list '((,a ,b) (,c ,d))
;                  `(let [quadruple ,(generate-quasiquote '(,a ,b ,c ,d) 'stx)]
;                     (pure ,(generate-quasiquote ''(four-elements ,quadruple) 'stx))))
;            (list '(keyword ,tail ...)
;                  `(pure ,(generate-quasiquote ''(keyword-prefixed (,tail ...)) 'stx))))))]))
(define-syntax (auto-splice stx)
  (racket-syntax-case stx (generate-quasiquote generate-syntax-case)
    [(_ ())
     #''()]
    [(_ (generate-quasiquote pat stx-name))
     #'(generate-quasiquote 'pat 'stx-name)]
    [(_ (generate-syntax-case macro-name stx-expr (keyword ...)
          [lhs rhs ...] ...))
     #'(generate-syntax-case 'macro-name 'stx-expr (list 'keyword ...)
         (list
           (list 'lhs
                 (auto-splice rhs) ...)
           ...))]
    [(_ (head tail ...))
     #'(cons (auto-splice head)
             (auto-splice (tail ...)))]
    [(_ x)
     #''x]))

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
                               [syntax-case raw-syntax-case]))
              '(import (rename (shift "prelude.kl" 1)
                               [syntax-case raw-syntax-case]))
              '(import (shift "identifier.kl" 1))
              '(import (shift "list-syntax.kl" 1))
              '(import (shift "temporaries.kl" 1))

              (generate-define-keywords (list 'fancy-unquote 'fancy-... 'fancy-_))
              (auto-splice
                (define-macros
                  ([fancy-syntax-case
                    (flet [list-of-keywords? (xs)
                           (generate-syntax-case fancy-syntax-case xs ()
                             [()
                              (pure (true))]
                             [(,x ,xs ...)
                              (pure (identifier? x))
                              (list-of-keywords? xs)]
                             [_
                              (pure (false))])]
                      (lambda (stx)
                        (generate-syntax-case fancy-syntax-case stx ()
                          [(_ ,stx-expr (,keywords ...) ,cases ...)
                           (let [stx-name 'stx]
                             (>>= (list-of-keywords? keywords)
                               (lambda (keywords-are-keywords)
                                 (if keywords-are-keywords
                                     (flet [is-identifier-in-list? (identifier xs)
                                            (generate-syntax-case fancy-syntax-case xs ()
                                              [()
                                               (pure (false))]
                                              [(,x ,xs ...)
                                               (>>= (free-identifier=? identifier x)
                                                 (lambda (same-identifier)
                                                   (if same-identifier
                                                       (pure (true))
                                                       (is-identifier-in-list? identifier xs))))])]
                                       (let [keyword?
                                             (lambda (keyword)
                                               (is-identifier-in-list? keyword keywords))]
                                         (flet [fancy-case (scrutinee-name case)
                                                (generate-syntax-case fancy-syntax-case case ()
                                                  [(,pat ,rhs)
                                                   (generate-syntax-case fancy-syntax-case pat (fancy-unquote fancy-... fancy-_)
                                                     [()
                                                      (pure (generate-quasiquote
                                                              (raw-syntax-case ,scrutinee-name
                                                                [() ,rhs]
                                                                [_ (failure-cc)])
                                                              stx))]
                                                     [fancy-_
                                                      (pure rhs)]
                                                     [,keyword
                                                      (pure (identifier? keyword))
                                                      (>>= (keyword? keyword)
                                                        (lambda (is-keyword)
                                                          (if is-keyword
                                                              (pure (generate-quasiquote
                                                                      (if (identifier? ,scrutinee-name)
                                                                          (>>= (free-identifier=? ,scrutinee-name ',keyword)
                                                                            (lambda (same-identifier)
                                                                              (if same-identifier
                                                                                  ,rhs
                                                                                  (failure-cc))))
                                                                          (failure-cc))
                                                                      stx))
                                                              (syntax-error (list-syntax
                                                                              ('"fancy-syntax-case: naked symbol"
                                                                               keyword
                                                                               '"did you mean (unquote symbol)?"
                                                                               '"did you mean to add the symbol to the keyword list?")
                                                                              stx)
                                                                            stx))))]
                                                     [(fancy-unquote ,x)
                                                      (if (identifier? x)
                                                          (pure (generate-quasiquote
                                                                  (let [,x ,scrutinee-name]
                                                                    ,rhs)
                                                                  stx))
                                                          (syntax-error (list-syntax
                                                                          ('"fancy-syntax-case: the syntax for binding values is (unquote x), found"
                                                                           pat
                                                                           '"instead")
                                                                          stx)
                                                                        stx))]
                                                     [((fancy-unquote ,x) fancy-...)
                                                      (if (identifier? x)
                                                          (pure (generate-quasiquote
                                                                  (let [,x ,scrutinee-name]
                                                                    ,rhs)
                                                                  stx))
                                                          (syntax-error (list-syntax
                                                                          ('"fancy-syntax-case: the syntax for binding lists is (,x ...), found"
                                                                           pat
                                                                           '"instead")
                                                                          stx)
                                                                        stx))]
                                                     [(,pat-head ,pat-tail ...)
                                                      (>>= (make-temporary 'tail)
                                                        (lambda (tail-name)
                                                          (>>= (fancy-case tail-name
                                                                 (pair-list-syntax pat-tail rhs
                                                                   stx))
                                                            (lambda (rhs-tail)
                                                              (>>= (make-temporary 'head)
                                                                (lambda (head-name)
                                                                  (>>= (fancy-case head-name
                                                                         (pair-list-syntax pat-head rhs-tail
                                                                           stx))
                                                                    (lambda (rhs-head)
                                                                      (pure (generate-quasiquote
                                                                              (raw-syntax-case ,scrutinee-name
                                                                                [(cons ,head-name ,tail-name)
                                                                                 ,rhs-head]
                                                                                [_ (failure-cc)])
                                                                              stx))))))))))]
                                                     [_
                                                      (pure (generate-quasiquote
                                                              (failure-cc)
                                                              stx))])])]
                                           (flet [fancy-cases (cases inner-cases)
                                                  (generate-syntax-case fancy-syntax-case cases ()
                                                    [()
                                                     (pure inner-cases)]
                                                    [(,case ,cases ...)
                                                     (>>= (fancy-case stx-name case)
                                                       (lambda (inner-case)
                                                         (fancy-cases cases
                                                           (generate-quasiquote
                                                             (let [failure-cc
                                                                   (lambda ()
                                                                     ,inner-case)]
                                                               ,inner-cases)
                                                             stx))))])]
                                             (>>= (fancy-cases cases
                                                    (generate-quasiquote
                                                      (failure-cc)
                                                      stx))
                                               (lambda (outer-cases)
                                                 (pure (generate-quasiquote
                                                         (let [,stx-name ,stx-expr]
                                                           (let [failure-cc
                                                                 (lambda ()
                                                                   (syntax-error (list-syntax
                                                                                   ('"fancy-syntax-case: the input"
                                                                                    ,stx-name
                                                                                    '"does not match any of the following patterns"
                                                                                    ',(map car cases))
                                                                                   stx)
                                                                                 stx))]
                                                             ,outer-cases))
                                                         stx))))))))
                                     (syntax-error (list-syntax
                                                     ('"fancy-syntax-case:"
                                                      keywords
                                                      '"does not look like a list of keywords."
                                                      '"did you forget a () between the input and the cases?")
                                                     stx))))))])))]
                   [fancy-quasiquote
                    (lambda (stx)
                      (generate-syntax-case fancy-quasiquote stx ()
                        [(_ ,pat)
                         (let [stx-name (generate-quasiquote
                                          ',(replace-loc pat 'here)
                                          'here)]
                           (flet [fancy-inside (pat)
                                  (generate-syntax-case fancy-quasiquote pat (fancy-unquote fancy-...)
                                    [(fancy-unquote ,x)
                                     (pure x)]
                                    [((fancy-unquote ,head) fancy-... ,tail ...)
                                     (>>= (fancy-inside tail)
                                       (lambda (inside-tail)
                                         (pure (generate-quasiquote
                                                 (append-list-syntax
                                                   ,head
                                                   ,inside-tail
                                                   ,stx-name)
                                                 stx))))]
                                    [(,head ,tail ...)
                                     (>>= (fancy-inside head)
                                       (lambda (inside-head)
                                         (>>= (fancy-inside tail)
                                           (lambda (inside-tail)
                                             (pure (generate-quasiquote
                                                     (cons-list-syntax
                                                       ,inside-head
                                                       ,inside-tail
                                                       ,stx-name)
                                                     stx))))))]
                                    [,x
                                     (pure (pair-list-syntax
                                              'quote
                                              x
                                              stx))])]
                             (fancy-inside pat)))]))])))

              '(export (rename ([fancy-syntax-case syntax-case]
                                [fancy-quasiquote quasiquote]
                                [fancy-unquote unquote]
                                [fancy-... ...]
                                [fancy-_ _])
                               fancy-syntax-case
                               fancy-quasiquote
                               fancy-unquote
                               fancy-...
                               fancy-_)))))))))
