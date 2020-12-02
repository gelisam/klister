Klister
------------

This repository contains a partial implementation of a macro expander
in which macros can get *stuck*. The idea is that if a macro depends
on information that will be the result of later macro expansion or
type checking, it can pause its execution until that information has
become available.

For a description of one way in which stuck macros might be useful,
please see this `talk`_.

.. _talk: https://www.youtube.com/watch?v=nUvKoG_V_U0


Installation
============

Klister is written in Haskell, and is built with HPack and Cabal. You can build
it like so::

    hpack package.yaml
    cabal v2-build

You can use ``v2-install`` instead of ``v2-build`` to install the Klister
executable and associated files to your home directory.

Usage
=====

Run ``klister repl`` to be dropped into a read-eval-print loop where you can try
out writing some Klister expressions.

``klister run file.kl`` will evaluate the examples and run the IO
actions in ``file.kl``.

Imports
~~~~~~~

The ``import`` form will search for modules in the same directory as the
importing module, and in directories listed in the ``KLISTERPATH`` environment
variable, a ``:``-separated list of directories.

Other Resources
===============

We presented the status of Klister as of Summer 2020 at the TyDe workshop. An `abstract`_ and a `recorded talk`_ are available.

.. _abstract: http://davidchristiansen.dk/pubs/tyde2020-predictable-macros-abstract.pdf
.. _recorded talk: http://davidchristiansen.dk/pubs/tyde2020-predictable-macros.webm

Overall Design
==============

The macro expander itself is a set-of-scopes expander, based on
`Matthew Flatt's paper`_ from POPL 2016 and described quite accessibly in
his talk from `Strange Loop`_.

.. _Matthew Flatt's paper: https://www.cs.utah.edu/plt/publications/popl16-f.pdf

.. _Strange Loop: https://www.youtube.com/watch?v=Or_yKiI3Ha4

Additionally, there is a module system patterned after `Racket's`_.

.. _Racket's: https://www.cs.utah.edu/plt/publications/macromod.pdf

This macro expander has a few differences:

* Rather than performing a depth-first traversal of the input syntax,
  expanding as it goes, our expander maintains a queue of expansion
  tasks. Tasks indicate the expression to be expanded as well as its
  resulting location in the final output. Dependency information is
  tracked in order to constrain the scheduling of expansion tasks.

* The core language does not coincide with the input language. Having
  an independent core language will hopefully allow us to overcome the
  overhead associated with recursive uses of ``local-expand``, as well
  as enabling a second, trusted type checking pass.

* Type checking and macro expansion are interleaved. Every expansion
  step in an expression or pattern context knows what type the
  resulting program will have.

The type checker is a mostly-vanilla Hindley-Milner, based on
Sestoft's description in `Programming Language Concepts`_, extended
with user-definable datatypes and Racket-style phase stratification of
bindings. It uses Rémy's optimization_ of generalization, where type
metavariables are assigned levels to avoid scanning the context at
generalization time.

.. _Programming Language Concepts: https://www.itu.dk/~sestoft/plc/

.. _optimization: https://hal.inria.fr/inria-00077006/document

FAQ
===

Why "Klister"?
--------------

"Klister" is Danish for "adhesive", and is also used to form words
describing *sticky* things. And our macros get *stuck*.
