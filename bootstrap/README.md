# bootstrapping

This file explains why we use Racket to generate some Klister code in order to
bootstrap our library of useful macros.


## the problem

The Klister `#kernel` provides a `syntax-case` macro, which I'll call
`raw-syntax-case` in this file. `raw-syntax-case` is minimalist: it only
supports shallow patterns. The idea is that deep patterns can and should be
implemented as a library, as a macro which I'll call `fancy-syntax-case`.

We must define `fancy-syntax-case` as a macro which expands to a number of calls
to `raw-syntax-case`. Because `fancy-syntax-case` is not yet defined, that macro
definition will need to pattern-match on its input using `raw-syntax-case`.
That's a bummer, because that makes the macro definition long and hard to read.

    (define-syntax (fancy-syntax-case stx)
      (raw-syntax-case stx
        [(cons _ scrutinee-keywords-cases)
         (raw-syntax-case scrutinee-keywords-cases
           [(cons scrutinee keywords-cases)
            (raw-syntax-case keywords-cases
              [(cons keywords cases)
               ...etc...])])]))

I would prefer to write that macro definition using `fancy-syntax-case` itself!
That would make the code much shorter and more readable.

    (define-syntax (fancy-syntax-case stx)
      (fancy-syntax-case stx
        [(_ ,scrutinee (,(keywords ... )) ,(cases ...))
         ...etc...]))

That sounds impossible, but there is a way!


## the solution

The trick is to write the short
readable definition that we want to write and to convert it into the long
unreadable definition. Writing this transformation using Klister would again
require using `raw-syntax-case`, so we use Racket instead.

We thus want to write a Racket program which expands `fancy-syntax-case` calls
into a number of calls to `raw-syntax-case`. But wait, we already have a program
which does that, it's the short readable definition we just wrote! Rather than
reimplement this Klister program in Racket, let's automatically translate this
program to Racket via a Racket `#lang`. Since the program assumes that
`fancy-syntax-case` already exists, this `#lang` must be a version of Klister in
which `fancy-syntax-case` is builtin. Thankfully, Racket's `syntax-case` (which
I will call `racket-syntax-case`) is already quite fancy, so we only need to
translate `fancy-syntax-case` calls into `racket-syntax-case` calls. We can do
this by writing a Racket macro.

The overall picture is that we used to have one daunting task:

1.  Use `raw-syntax-case` to expand `fancy-syntax-case` into a number of calls
    to `raw-syntax-case`.

And we now have two easier tasks:

1.  Use `fancy-syntax-case` to expand `fancy-syntax-case` into a number of calls
    to `raw-syntax-case`.
2.  Use `racket-syntax-case` to expand `fancy-syntax-case` into a call to
    `racket-syntax-case`.


# the scope

The above argument also applies to `quasiquote`, which is also very useful when
defining other macros. By defining both `fancy-syntax-case` and
`fancy-quasiquote` at the same time using the above technique, we get to use
both `fancy-syntax-case` and `fancy-quasiquote` when defining both macros. This
is thus a technique which becomes more useful as we define more macros
simulaneously. We may thus add more macros to the list in the future.
