
mindless-coding, phase 2
========================

Please refer to https://github.com/jonleivent/mindless-coding for phase 1 of
this project.

Phase 2 will concentrate more on the tactic infrastructure and proof
techniques, in an attempt to make them easier to use (phase 1 was a hodgepodge
of many different techniques without much clarity - mostly just a proof of
concept).

This site uses Coq version 8.5. The exact file coq-version-used will be
updated with the output of coqtop --version, and the file coq-githash-used
will be updated with the git hash (as reported by coqtop -batch for
development versions) for the exact Coq build used.  However, all attempts
will be made to keep compatibility with the released 8.5 version.

First up: a rewrite of gaptrees, renamed to wavltrees, and made to correspond
more closely with the work on weak-AVL trees at Princeton as reported in
http://www.cs.princeton.edu/~sssix/papers/rb-trees-talg.pdf.  Those familiar
with phase 1 of this project will recall that weak-AVL trees (gaptrees) were
"discovered" by accident there, but the Princeton group has claim to finding
them first.

------------------------------------------------------------------------

Dependent Type-Directed Development (a.k.a "Mindless Coding").

The point of this exercise is best seen by comparing the Coq sources wavl.v
and wavl-noninter.v to their respective extracted OCaml output files wavl.ml
and wavl-nointer.ml.

First, the reason I have provided both wavl.v and wavl-noninter.v is that the
latter is perhaps more "programmer-friendly" to many, especially those
unfamiliar with Coq's interactive proof mode.  Note that they both generate
nearly identical OCaml code (compare wavl.ml to wavl-noninter.ml, and note
that virtually all differences between them involve just variable renamings).
Even though I am a software developer, and certainly not a type theorist, I
have come to favor use of Coq's interactive proof mode for its ability to
guide one to a solution - providing: Interactive Dependent Type-Directed
Development.

Back to the main result: Note how the main wavltree functions (find, rot1,
rot2, insert, drot1, drot2, delmin, delmax and delete) in the primary input
files (wavl.v and wavl-noninter.v) closely follow the generated OCaml code
(wavl.ml and wavl-noninter.ml).  But, note the important difference: although
the control flows in the functions are apparent in the .v files, the function
"leaves" (the terms returned at the end of each control path) are all filled
in using Coq's proof search via tactics.  This is only possible due to the
very dependent nature of the function specifications (argument and return
types), as well as the very dependent nature of the data structure (wavltree)
itself.  As a result, the functions in the primary .v files are far easier to
"code" (the distinction between proving and coding disappears) than they would
be if the user was coding directly in the output language (OCaml), as well as
being guaranteed (modulo Coq's trustworthiness, as well as that of the
invariants specified in the dependent types) to be correct, as well as being
generated (in the .ml files) completely unburdened by proof-required parts.

------------------------------------------------------------------------

What are the underlying contributions enabling this result?:

1. True Erasability.  I wish Coq had this built in, but it doesn't (Idris
does, but Idris was still not quite mature enough to handle the other
complexity of this project last I checked; Agda doesn't have true erasability,
but can handle the other complexity).  Instead, Coq's erasure of Props and
some type args has to be enhanced via. erasable.v.  However, when this is done
(with sufficient care so as not to become inconsistent), the OCaml output code
is as good as one would expect from an expert developer, and is completely
free of all required-only-for-proving elements.  Claiming this as a
"contribution" is perhaps claiming too much, as this kind of erasability has
been suggested before.  However, this project attempts to demonstrate how
important a feature this is (or would be).

As the erasability feature is implemented here (Coq Props + erasable.v), one
important detail for nay-sayers to notice is that the impact on the Coq source
files wavl.v and wavl-noninter.v is very minor.  While it is true that certain
types need to be mirrored as erasable types (EZ for Z, EB for bool, EL for
list A), as well as certain functions, the definitions are trivial.

Another important detail is that implementations of erasability similar to
this one (as opposed to Coq's "Extraction Implicit" mechanism, for example)
prevents automated proof search, as well as the programmer, from accidentally
using elements marked for erasure in a way that prevents their eventual
erasure.

2. Specialized (semi)decision procedures for types used in specifications.
The files sorted.v and solvesorted.v provide a (semi)decision procedure (semi
only because I haven't determined it is complete, but it has held up under
considerable stress) for sorted lists of arbitrary elements.  The Examples at
the end of solvesorted.v demonstrate some of what this decision procedure can
decide.

The file ezbool.v provides a (semi)decision procedure (or, rather enhances the
already existent ones omega and ring) for bools and integers (Z).  The
enhancements enable multi-goal solution using Coq's (new to version 8.5)
backtracking proof search capabilities, including techniques for the solution
of subgoals sharing existential variables (evars).  I believe this may be one
of the first Coq developments to exploit backtracking in this way.

As a result, it becomes very easy to write small specialized proof-search
tactics (solve_find, solve_wavl, solve_insert, etc.) for each function, and
use them in a predictable and consistent way to remove the burden of algorithm
implementation - even in cases where one does not know the algorithm, nor even
know if an algorithm exists (as was the case with wavltrees/gaptrees).

The important point to these (semi)decision procedures is that they are
generic - nothing about them restricts their usage to wavltrees, or to just
binary trees, etc.  They are developed once, and should be usable by a large
variety of dependent-type driven developments (although they may not be
sufficiently complete yet).


