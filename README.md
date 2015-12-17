
mindless-coding, phase 2
========================

Please refer to https://github.com/jonleivent/mindless-coding for phase 1 of
this project.

Phase 2 will concentrate more on the tactic infrastructure and proof
techniques, in an attempt to make them easier to use (phase 1 was a hodgepodge
of many different techniques without much clarity - mostly just a proof of
concept).

This site will use Coq version 8.5 when it is released - currently, it is
using a recent development version of Coq from
git://scm.gforge.inria.fr/coq/coq.git.  The file coq-version-used will be
updated with the output of coqtop --version, and the file coq-githash-used
will be updated with the git hash (as reported by coqtop -batch for
development versions) for the exact Coq build used.

First up: a rewrite of gaptrees, renamed to wavltrees, and made to correspond
more closely with the work on weak-AVL trees at Princeton as reported in
http://www.cs.princeton.edu/~sssix/papers/rb-trees-talg.pdf.  Those familiar
with phase 1 of this project will recall that weak-AVL trees (gaptrees) were
"discovered" by accident there, but the Princeton group has claim to finding
them first.
