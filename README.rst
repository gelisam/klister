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


Overall Design
==============

The macro expander itself is a set-of-scopes expander, based on
`Matthew Flatt's paper`_ from POPL 2016 and described quite accessibly in
his talk from `Strange Loop`_.

.. _Matthew Flatt's paper: https://www.cs.utah.edu/plt/publications/popl16-f.pdf

.. _Strange Loop: https://www.youtube.com/watch?v=Or_yKiI3Ha4

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

We additionally intend to eventually interleave a type checker with
the macro expander, but there's not yet any evidence of this in the
source code.


Initially, macros can get stuck by blocking until a signal has been
sent. Signals are essentially just integers. Other macros can send
signals, at which point the blocked macros get un-stuck. This is
reminiscent of the ``blockOnMeta`` operation in Agda's reflection
system. Eventually, we plan to replace this with the ability to block
on the solution to a metavariable.

FAQ
===

Why "Klister"?
--------------

"Klister" is Danish for "adhesive", and is also used to form words
describing _sticky_ things. And our macros get _stuck_.
