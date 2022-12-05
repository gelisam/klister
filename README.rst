Klister
------------

Klister [`TyDe 2020`_, `video`_] is a is a programming language, a research
prototype which combines features from Racket, ML, and a strict Haskell into a
single language. It is named after its most distinguishing feature, "stuck
macros" [`Compose NYC 2019`_], as "Klister" is Danish for "adhesive".

.. _TyDe 2020: http://davidchristiansen.dk/pubs/tyde2020-predictable-macros-abstract.pdf
.. _video: https://www.youtube.com/watch?v=FyeWwYfqTHo
.. _Compose NYC 2019: https://www.youtube.com/watch?v=nUvKoG_V_U0

::

  #lang "prelude.kl"

  -- do notation is not builtin syntax, it's implemented as a library!
  (import "monad.kl")

  -- An effectful action whose inferred type is (-> String (IO Unit))
  (defun putStrLn (str)
    (write stdout (string-append str "\n")))

  -- "run" is like main, except you can have more than one.
  (run
    -- Klister doesn't have type classes yet, so "do" needs an explicit
    -- dictionary argument.
    (do io-monad
      (putStrLn "hello")
      (putStrLn "world")))

You can run the above program using either stack or cabal::

    $ cabal run klister -- run examples/hello.kl
    hello
    world

Features
========

Features we borrow from Racket:

* `Custom syntax`_, via `hygienic macros`_ with `easy-to-override hygiene`_.
* `Custom languages`_ (``#lang``), via macros which reinterpret terms into
  those of an existing ``#lang``.
* `Syntax objects`_, that is, s-expressions annotated with source locations and
  lexical information.
* A `module system`_ which respects the `phase system`_. Thus, if Klister one
  day supports generating binaries, those binaries will not be unnecessarily
  clogged with dependencies which were only needed at compile-time.

.. _Custom syntax: examples/lambda-case.kl
.. _hygienic macros: TODO: write a short example demonstrating lack of capture.
.. _easy-to-override hygiene: examples/anaphoric-if.kl
.. _Custom languages: examples/rpn.kl
.. _Syntax objects: TODO: link to a short example which explains that in
   Racket, syntax objects are introduced via ``#'(...)``, whereas in Klister
   they are introduced via ``'(...)``. Also explain that Klister does not have
   unannotated s-expressions. And the relationship between Syntax and
   Syntax-Contents.
.. _module system: TODO: write a short example demonstrating how to use the
   import and export primitives.
.. _phase system: TODO: write a short example demonstrating macros which
   generate macros. Maybe define-syntax-rules.kl?

Features we borrow from ML:

* A type system with `parametric polymorphism`_, `algebraic datatypes`_, and
  Hindley-Milner `type inference`_.

.. _parametric polymorphism: TODO: write a short example demonstrating the
   feature, like id or fmap.
.. _algebraic datatypes: TODO: write a small example defining and matching on
   an algebraic type. Perhaps Either?
.. _type inference: TODO: write a small example demonstrating that type
   information flows in two directions.

Features we borrow from Haskell:

* Monadic macros; our macros have type ``(-> Syntax (Macro Syntax))``, where
  ``Macro Syntax`` is similar to ``Q Exp`` in TemplateHaskell. Note that this
  type implies that a macro is allowed to generate ill-typed code; this error
  is caught where the macro is called, not where the macro is defined. We thus
  aim for the expressivity of Template Haskell, not the extra guarantees of
  Typed Template Haskell.
* Purely functional; primitives with compile-time side-effects (e.g. comparing
  identifiers while taking into account the current set of bindings) run in the
  ``Macro`` monad, while primitives with runtime side-effects (e.g. printing to
  stdout) run in the ``IO`` monad.
* Higher-kinded types; for example `monads`_ are defined as a library.

.. _monads: TODO: link to monad.kl's Monad definition, and add a comment there
   highlighting the inferred type, especially the higher-kinded type variable.

Features which make Klister special (but not necessarily *unique*; see the
`bibliography`_ for languages with similar features):

* `Type-providing macros`_; a macro can provide type information about the
  code it plans to generate.
* `Type-aware macros`_; a macro can obtain type requirements about the code it
  needs to generate.
* `Stuck macros`_; the above two features make it possible for macros to
  communicate, and thus to affect what each other generates. The language
  primitives are designed so that the order in which the macros are expanded
  cannot affect their results, and indeed the same is true for the order in
  which the macro expansion and type-inference steps are interleaved. This
  means that the order in which the type checker traverses a program and
  generates constraints is not visible to the authors of macros, providing a
  predictable programming model. This makes Klister code more robust to
  refactorings which affect that order.
* `Problem-aware macros`_; in addition to the type, a macro can learn which
  "problem" it needs to solve, namely whether it must generate an expression, a
  type, a pattern, etc. Each problem would correspond to a form of judgment if
  the language was formalized, e.g. a typing judgment for the `expression`
  problem, a well-formed type judgment for the `type` problem, etc.

.. _bibliography: bibliography.rst
.. _Type-providing macros: TODO: write a small example demonstrating this
   feature.
.. _Type-aware macros: TODO: write a small example demonstrating this feature.
.. _Stuck macros: TODO: write a small example demonstrating this feature. Maybe
   the traverse-traverse-id example from Compose NYC 2019?
.. _Problem-aware macros: TODO: write a small example demonstrating all the
   different problems one can write a macro for.

Cool things which can be built using the above features:

* Macros communicating via types
* `Custom type-driven code generation`_, via macros which generate code from a
  type.
* Languages with `custom type systems`_, via macros which reinterpret types
  into those of an existing ``#lang``, and which contribute to type inference
  by providing type information about the code they generate. The variety of
  type-systems which can be implemented this way is unforunately limited by
  the core type system to which everything must be rewritten.
* Languages with `custom implicit terms`_, via macros which generate terms of
  an existing ``#lang`` based on a type in the new ``#lang``.

.. _Custom type-driven code generation: TODO: write a small example
   demonstrating the feature. Perhaps the traverse-traverse-id example again?
.. _custom type systems: TODO: write an example #lang in which functions are
   not curried, writing copious comments.
.. _custom implicit terms: TODO: improve the comments in the
   implicit-conversion example, then link to it.

While we think Klister demonstrates some neat ideas, there are some limitations
which make Klister an impractical choice for most real-life projects. If you
want to help make Klister a more practical language, please `reach out`_!

.. _reach out: https://github.com/gelisam/klister/issues/new

Here are the most prominent Racket features which are missing from Klister:

* Klister does not yet support custom readers, and thus every ``#lang`` looks like a
  Lisp. This also limits languages to Integer literals and String literals.
* `local-expand`_ is planned, but not yet implemented.
* `Syntax parameters`_ are planned, but not yet implemented.

.. _local-expand: https://github.com/gelisam/klister/issues/144#issuecomment-1133964551
.. _Syntax parameters: https://github.com/gelisam/klister/issues/105

Here are the most prominent Haskell features which are missing from Klister:

* `Type classes`_ are planned as a library, but are not yet implemented.
* `Type annotations containing foralls`_ are planned, but not yet implemented.
  Currently, Klister only supports type ascriptions, e.g.
  ``(+ (the Integer (* 2 3)) 1)``, for giving the type of a sub-expression.
* Klister does not support GADTs nor type families.

.. _Type classes: https://github.com/gelisam/klister/issues/167
.. _Type annotations containing foralls: https://github.com/gelisam/klister/issues/60

Here are the most prominent features which Racket and Haskell both have but
which are missing from Klister:

* Klister is missing commonly-expected datatypes like ``Map``, ``Set``, and
  ``Double``.
* Klister requires functions and datatypes to be defined before they are used.
* Klister does not support concurrency. It might be possible to implement a
  ``#lang`` with a green thread scheduler.
* Klister does not support exception-handling. ``error`` and ``syntax-error``
  both terminate the program immediately, like ``panic!`` in Rust. It is
  definitely possible to implement ``Either``-based error handling, and it
  should be possible to implement a ``#lang`` in which exceptions are an
  ambient effect.
* Klister does not have a rich ecosystem of libraries. It does not have a
  package repository where individual contributors can release their own
  packages. Please upload your Klister code to the `examples`_ folder, it
  currently contains all the Klister code which was ever written.
* Klister does not have a rich set of IO primitives out of which you could
  build all the libraries you need yourself. Currently, you can only print to
  stdout.
* A Foreign-Function-Interface (`FFI`_), to reuse Haskell's rich ecosystem of
  libraries (and its own FFI to C), is planned but not yet implemented.
* `Expanding modules separately`_, to speed up expansion times, is planned
  but not yet implemented.
* Klister does not produce binary executables.

.. _examples: https://github.com/gelisam/klister/tree/main/examples
.. _FFI: https://github.com/gelisam/klister/issues/165
.. _Expanding modules separately: https://github.com/gelisam/klister/issues/118

Guide and Reference
===================

The Klister Guide consists of the various commented examples linked from the
above feature list, plus the extra information in the sub-sections below.

The Klister Reference covers every identifier in the "prelude.kl" language, but
doesn't currently say much about each. It consists of a `list of examples`_
showing how to use the macros, and a `list of type signatures`_ documenting how
to use the values and functions.

.. _list of examples: examples/primitives-documentation.kl
.. _list of type signatures: examples/primitives-documentation.golden

Imports
~~~~~~~

The ``import`` form will search for modules in the same directory as the
importing module, and in directories listed in the ``KLISTERPATH`` environment
variable, a ``:``-separated list of directories.
