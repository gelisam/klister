Bibliography
============

This annotated bibliography is very much under construction!

Macros and module systems
-------------------------

The overall macro expander uses Flatt's set-of-scopes algorithm for hygiene: https://www.cs.utah.edu/plt/publications/popl16-f.pdf

The module system is based on Racket's: https://www.cs.utah.edu/plt/publications/macromod.pdf

We'd like to find a way to do the things described in `Macros that Work Together`_, but with types. It's mostly just design sketches so far for us. We expect that we can adapt the design of `MetaPRL's resources`_ to replace compile-time bindings, at least.

.. _Macros that Work Together: https://www.cs.utah.edu/plt/publications/jfp12-draft-fcdf.pdf

.. _MetaPRL's resources: http://web.archive.org/web/20061005013840/http://files.metaprl.org/papers/metaprl.pdf

Type checker implementation
---------------------------

The type checker is based on Sestoft's description in `Programming Language Concepts`_. It uses Rémy's optimization_ of generalization, where type metavariables are assigned levels to avoid scanning the context at generalization time.

LVars have been used to `parallelize type checkers`_.

.. _Programming Language Concepts: https://www.itu.dk/~sestoft/plc/

.. _optimization: https://hal.inria.fr/inria-00077006/document

.. _parallelize type checkers: https://dl.acm.org/doi/10.1145/2851141.2851142


Related Work
------------

These systems have some form of type-aware hygienic macro, or other typed metaprogramming.

Lean
~~~~

`Lean's macros`_ are the closest thing to Klister right now.

.. _Lean's macros: https://arxiv.org/pdf/2001.10490.pdf

Scala
~~~~~

* https://infoscience.epfl.ch/record/257176?ln=en

  - Precursor: https://github.com/epfldata/squid#publications

MetaML
~~~~~~

MetaML_ is a staged programming system rather than a macro system, but it pays to be familiar with it.

.. _MetaML: https://doi.org/10.1016/S0304-3975(00)00053-0

MacroML
~~~~~~~

MacroML_ compiles down to MetaML, and thus provides very strong guarantees. It's less expressive than a full procedural macro system, though.

.. _MacroML: https://dl.acm.org/doi/10.1145/507635.507646
