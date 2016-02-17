(***********************************************************************

Copyright (c) 2016 Jonathan Leivent

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

 ***********************************************************************)

Require Import elist.
Require Import ezbool.
Require Import ExtrOcamlBasic.
Require Import utils.
Require Import posall.
Require Import hypiter.

Generalizable All Variables.
(*Generalizable All Variables just means that by prefixing an arg binding with
`, we tell Coq to find all undeclared variables in that binding and declare
them as implicit args.  This tends to make function and constructor signatures
easier to read.*)

(* Since we are using Context commands to make A and ordA implicit args of
everything, we should be enclosing everything in a single Section.  However,
Coq does not allow the use of Extraction commands within a section.  Also, the
extra "ordA" arg added by the Section to every function just complicates the
extracted code a bit.  So comment out the section for now. *)
(* Section Wavltree. *)

Context {A : Set}.
(*A is the Set of elements.  We have to restrict ourselves to Set in order to
avoid introducing an inconsistency through Erasable.  However, we use
-impredicative-set to enlarge what a Set can be.*)

Context {ordA : Ordered A}.
(*Put typeclass Ordered on A, so that we can compare A's and sort them.*)

Notation EL := ##(list A). (*erasable lists of our element type A*)

Inductive wavltree(k : EZ)(g lg rg : EB) : EL -> Set :=
(* Type of wavltrees (weak-AVL trees) with rank k, gap g, child gaps lg and rg
(for left and right children respectively), with its contents (as a flattened
list of all elements in sorted order) as its only type index.  It makes sense
to keep contents as the one type index, so that it is used to limit both
inversions of existing wavltrees and constructions of new ones based on the
contents.  It does not make sense to make the other parameters into type
indexes because we want them interpreted semantically and not by pattern.  In
other words, we want just enough green slime, but not too much.

The rank is as used in the Princeton articles on weak-AVL trees.  The "gaps"
are just the relationships between parent and child ranks - if a child is at
rank k and the parent is at rank k+1, then there is no "gap" between them -
they are a close as possible in rank.  Otherwise, the child is at rank k and
the parent is at rank k+2, and there is a gap.  These wavltrees only allow one
bit gaps for that one extra rank separation.  If we want to allow wider gaps,
we would need more bits to encode the wider gaps width.

Why do we expose so much of the internals of a wavltree through its type
parameters and indexes?  This turns out to make it very convenient to test
and/or limit cases of wavltrees in the proofs without having to use projection
functions.  We will keep all type parameters and indexes erased - because,
despite the promise that type parameters are automatically erasable by default
(meaning, without wrapping them in the Erasable type), relying on this would
induce unerasable arguments in functions and constructors at usage points of
wavltree that aren't automatically erasable.

Note that we stick to 3 erasable types - EZ (erasable Z integers), EB
(erasable bools), and EL (erasable A lists) - because we have developed
powerful tactics for dealing with these types.  More accurately: we have
developed tactics for solving equalities in EZ that include usage of the
conversion function Eb2Z : EB -> EZ, and we have developed tactics for solving
Esorted goals and ENotIn goals on ELs. *)
| Missing
    (*Missing represents something that isn't there - a "null" value.  Despite
    this, it can have fields in Coq, provided they are all erasable.  That's
    quite convenient, actually - as it allows us to encode the all-important
    rank value (k) so that we don't have to repeatedly ask if a particular
    wavltree is Missing or not before using its rank in (erased) formulas.  We
    choose -1 as the rank for Missing wavltrees, as is done in the Princeton
    articles. *)
    (eqk : k = #(-1))
    (*It's also similarly convenient to provide false as the erased value for
    the erased lg and rg fields.  Obviously, a Missing node has no children,
    but these fake values allow for proofs that again don't bother to check if
    a wavltree is Missing or not and which don't need to rely on projection
    functions.  In this case, the tryLowering function is simplified by making
    these both false - as otherwise, the tryLoweringResult would need a
    separate constructor for the Missing case, instead of using the TLtooLow
    constructor for that case.*)
    (eqlg : lg=#false)
    (eqrg : rg=#false)
    (*Note that we didn't constrain the type parameter g for this Missing ctor
    - this amounts to allowing the gap value of a Missing node to "float" in
    the proofs - whatever value the proof thinks it should have, it can have.
    Ok - so how do we know in advance whether it will be more convenient in
    cases like this (where there are no unerased fields constraining our
    erased type parameters) to use a dummy value or allow it to float?  With
    g, unlike k, lg and rg, we would like to be able to set a wavltree node's
    gap using a trivial function (setgap), and have that respected in the
    proofs even if there's no gap bit to set.  We don't do the same with k, lg
    and rg because these represent more complex structure within a wavltree
    that we wouldn't want to be able to change so easily.  It's weird enough
    that we can have dummy values for erased fields, it's even weirder that we
    can pretend to change values in these fields - but it works out quite well
    in the proofs - they don't spend much time at all asking if a particular
    wavltree is Missing or not before just diving in.*)
  : wavltree k g lg rg []
| Node
    (*Unlike Missing, Nodes do contain their gaps as real "unerased" boolean
    values (ug), so we need to make sure the correspondence between the erased
    type parameter (g) and an unerased boolean field ug is maintained (by
    proof witness equg)*)
    (ug : bool)
    (equg : g = #ug)
    (*The relationship of a Node's rank (k) to its childrens' ranks (lk and
    rk) and childrens' gaps (lg and rg) is contained in equations eqlk and
    eqrk.  Note that b2Z, and its erased variant Eb2Z, just convert a boolean
    to an integer in the usual way (false->0, true->1).  The tactic (boom)
    that automates solutions to equations involving ranks and gaps is good
    enough such that the exact form of these equations here doesn't matter -
    we could write eqlk instead as lk #+ #1 = k #- Eb2Z lg, or any equivalent.
    However, placing eqlk before lc (and eqrk before rc) does help speed up
    the proof search a bit - as that same tactic for solving equations with
    ranks and gaps can do constraint propagation of sorts when there are
    unknowns (evars), but can only say "yeah or nay" when there are no
    unknowns. *)
    `(eqlk : lk = k #- #1 #- Eb2Z lg)
    `(lc : wavltree lk lg llg lrg lf) (*left child*)
    (d : A) (*datum*)
    `(eqrk : rk = k #- #1 #- Eb2Z rg)
    `(rc : wavltree rk rg rlg rrg rf) (*right child*)
    (s : Esorted (lf++^d++rf)) (*constrain the contents to be sorted*)
    (*The leaf arg proof witness disallows the creation of Nodes at rank 1
    that have only Missing children - in other words, leaves.  Thus, we
    require all leaves to be at rank 0.  Said differently, a node with rank 1
    must have at least one non-missing child - hence at least one child with
    rank 0.  It doesn't matter much how we express this - for instance, we
    could say k=#1 -> lg=#false \/ rg=#false.  We could even say k=#1 ->
    lf<>[] \/ rf<>[].  Why do we know in advance that Nodes at rank 1 must not
    be leaves?  Because otherwise how would we be able to distinguish leaves
    at rank 0 from leaves at rank 1 at runtime?  All of the relevant info
    would be erased by then, unless we kept unerased ranks around at runtime,
    which would just waste resources.  If we instead recorded the gaps in the
    parent nodes - as does the classic AVL tree, then that would also be a way
    to allow for leaves at both rank 0 and 1.  But, we wish to have just one
    bit of balance info per node, not two (as with classic AVL trees) - hence
    we store the gap bit on each child (that isn't Missing).  Also, this
    frugality with balance bits is quite fortuitous, as this leaf condition
    turns out to be necessary for the wavltree proofs to go through without
    forcing AVL-like multiple rotations during delete.  Instead, we get the
    better-behaved red-black-tree-like O(1) rotations per delete - in fact, we
    get at most 1 rotation per any operation, insert or delete.  Found by
    luck!  And frugality! *)
    (leaf : k=#1 -> lk=#0 \/ rk=#0)
  : wavltree k g lg rg (lf++^d++rf).

Lemma wavlkgtm1 :
  forall `(t : wavltree ek g lg rg f), exists k, #k=ek /\ k >=-1.
(*The downside to using Z (integers) for rank instead of nat (naturals) is
that we have to prove the lower bound.  Not a big deal, but necessary.
Originally, I used nat - but in this exposition I wanted ranks to correspond
directly to ranks as discussed in the Princeton articles, where they use rank
-1 for missing nodes.

Note that we don't formulate this as

 forall `(t : wavltree #k g lg rg f), k >= -1

because then this lemma would only be applicable to wavltree instances that
have an unerased rank, as Coq determines applicability via unification.  We do
have some tactics that can "force" applicability when unification isn't
sufficient, but there is no need to use them here.  The unerase tactic, which
is used by bang, handles existentials like "exists k, #k=ek /\ k >=-1"
automatically.  *)
Proof.
  dintros.
  (*dintros is a variant of intros that also does destruction of conjunctions
  and substitution of variables - but doesn't do intro patterns, because we
  will be trying not to rely on names of hypotheses other than those that are
  arguments.  We don't even want to rely on the number or relative order of
  intro pattern parts.*)
  induction t.
  all:bang.
  (*boom would work in all cases where we use bang - I'm just using bang to
  highlight the fact that there are no evars present.*)
Qed.

Lemma wavlkge0 :
  forall `(t : wavltree ek g lg rg f), f<>[] -> exists k, #k=ek /\ k>=0.
(*If the wavltree isn't empty, then the lower bound on its rank is 0, not -1.
Proving it once just saves the proof automation some wear.*)
Proof.
  dintros.
  simple inversion t; dintros.
  - bang.
  - posall @wavlkgtm1.
    (*posall finds all ways to pose a particular lemma in a proof context.*)
    bang.
Qed.

Lemma wavlfnenil :
  forall `(t : wavltree k g lg rg f), k <> #(-1) -> f<>[].
(*There's really two ways to tell if a wavltree is not missing.  One is based
on the type index not being [].  The other is based on its rank not being -1.
Mostly, we compute ranks in the proofs, and then want to know of based on that
which trees are not missing - so this allows us to do that.*)
Proof.
  dintros.
  simple inversion t; bang.
Qed.


(*When a particular wavltree instance is found to be Missing, we normally
would like to just remove it from the proof context and replace it with
sufficient info noting it was missing.  The following two lemmas, clearleaf1
and clearleaf2, enable this.

Note that we don't need these to be general cases, unlike the above - so we
don't mind that Coq's unification will only allow clearleaf1 in cases where
the rank is directly unifiable with #(-1), and clearleaf2 in cases where the
contents are directly unifiable with []. *)

Lemma clearleaf1 :
  forall `(t : wavltree #(-1) g lg rg f), f=[] /\ lg=#false /\ rg=#false.
Proof.
  dintros.
  posall @wavlkge0.
  simple inversion t; bang.
Qed.

Lemma clearleaf2 :
  forall `(t : wavltree k g lg rg []), k=#(-1) /\ lg=#false /\ rg=#false.
Proof.
  dintros.
  simple inversion t; bang.
Qed.

Ltac bang_setup_tactic ::=
(*We mentioned that the bang tactic is a subpart of the boom tactic.  The boom
tactic will be used to solve equalities involving ranks and gaps, whether they
have unknowns (evars) or not.  The bang tactic is the part used when there are
no unknowns - it merely succeeds or fails with no impact on other "sibling"
goals.  In such cases, we have to determine if the equality is solvable
instead of propagating constraint info (through evars) to other sibling goals
- so we need all relevant info about ranks and gaps available in the proof
context.  The bang_setup_tactic, redefined here (it defaults to idtac), is
called by bang as a way to "prime" the context with all such available info,
using some of the lemmas we just defined.*)
  let f H :=
      lazymatch type of H with
      | wavltree _ _ _ _ _ =>
        (*get the most specific info we can:*)
        first [apply clearleaf1 in H
              (*clearleaf1 will fail if rank is not #-1*)
              |apply clearleaf2 in H
              (*clearleaf2 will fail if contents are not []*)
              |pose proof (wavlkge0 H ltac:(assumption||fnenil))
              (*wavlkge0 will fail if that ltac can't prove the contents aren't []*)
              (* fnenil is a tactic that can prove things like A++^x++B<>[]
                 whenever there's an "^x" present*)
              |pose proof (wavlkgtm1 H) (*most generic, last resort*)
              ]
      | _ => idtac
      end
  in
  (*the hyps => loop form is an iterator over hypotheses.  This might get
  replaced by Gregory Malecha's plugin foreach tactic later.*)
  hyps => loop f.

Definition isMissing`(t : wavltree ek g lg rg f)
  : {f=[] /\ lg=#false /\ rg=#false /\ exists k, #k=ek /\ k=-1}
    + {f<>[] /\ exists k, #k=ek /\ k>=0}.
(*Sometimes, we would like to determine if a wavltree is missing or not
without having to invert it (corresponding to a match on it in the extracted
code).  This function does this, and also adds relevant info into the proof
context, which is probably not necessary because the bang_setup_tactic would
find this info itself.  But, we do it anyway. *)
Proof.
  destruct t;constructor;bang.
Qed.

Lemma wavls :
  forall `(t : wavltree k g lg rg f), Esorted f.
(*This is just projecting out the Esorted s field of Node, along with the fact
that [] is sorted by virtue of being empty.  It's useful for priming the proof
context with all available Esorted information, similar to how
bang_setup_tactic primes the proof context with all available rank
information.*)
Proof.
  dintros.
  onhead wavltree destr.
  (*onhead is a way to indicate a particular hypotheses based on its type's
  identifier (head), instead of by name.  So, "onhead wavltree destr" is
  equivalent here to "destruct t", as t is the only wavltree in the proof
  context.  Note "destr" instead of "destruct" - this is just an artifact of
  Coq's peculiar Ltac syntax, where even though "destruct" looks like an Ltac
  function, it is really just a notation.  "destr" is defined as: Ltac destr H
  := destruct H.*)
  - unerase.
    (*Unerase is a general tactic that attempts to convert all erased
    variables in a proof context into unerased ones - but it can only do this
    when the goal is a Prop (hence itself erased).  If the goal is not a Prop,
    then there are still a few things unerase can do, such as convert
    equalities like #A=#B into A=B.*)
    solve_sorted.
    (* The solve_sorted tactic is a "decision" procedure for sorted lists and
    their sorted sublists.  On rare occasion, solve_sorted shows itself to not
    be a decision procedure, but it has lately held up quite well.  Ideally,
    tactics like solve_sorted and boom would be made iron-clad, as they are
    generally useful beyond just this one project. *)
  - assumption.
Qed.

Ltac ss_setup_tactic := 
(*Analogous to bang_setup_tactic - this does the same for ss:*)
  let f H := try apply wavls in H in
  hyps => loop f.

Ltac ss :=
(*We'll use ss for solving any goal with an Esorted conclusion.*)
  ss_setup_tactic; unerase; solve[solve_sorted].

(*First example - the find function*)

(*With all functions, we will define a result type that specifies the the
result we want rather precisely.  Much of that precision will be encoded in
erased lists of contents.  Here, findResult is parameterized by the element
being searched for, and indexed by the contents of the wavltree being searched
in.  To give a Found result, we must present the contents index such that the
searched for element is shown in its actual position in the contents.  For
NotFound, we provide a proof that the element is not present in the
contents.*)

Inductive findResult(x : A) : EL -> Set :=
| Found{fl fr} : findResult x (fl++^x++fr)
| NotFound{f} : ENotIn x f -> findResult x f.

Ltac solve_find :=
(*Piece together a tactic to solve findResults.*)
  dintros;
  reassoc;
  (*reassoc is a tactic that provides, via backtracking, all necessary
  re-associated alternatives of erased lists in the conclusion.  In other
  words, given a conclusion containing something like A++B++C++D (note ++ is
  right-associative, hence A++B++C++D is A++(B++(C++D))), it will provide
  A++B++C++D, (A++B)++C++D, and (A++B++C)++D as its 3 consecutive successes,
  and then fail if attempted again (as there are no other forms differing only
  by top-level associativity - ((A++B)++C)++D is excluded by the top-level
  aspect).  This allows us to discover the necessary associativity via proof
  search.  We only ever need top-level associativity to be searched because we
  construct or destruct one level of tree at a time - hence other levels of
  associativity, if needed, will be visited when constructing/destructing
  those levels of the trees involved.*)
  (eapply Found + (eapply NotFound; ss)).

Definition find(x : A)`(t : wavltree k g lg rg f) : findResult x f.
(* The above signature is a complete specification with respect to all
externally visible behavior of find, except for its performance.  By using a
dependently-typed result instead of bool, and by tying that dependently-typed
findResult appropriately to the input, we guarantee that the resulting
function - if one can be found (proved) - will only report Found when x does
exist in t, and NotFound only when x does not exist in t.  We can't specify
performance yet - that would probably require linear logic.  Note that this
specification omits internal details such as how much of the tree is
searched.*)
Proof.
  onhead wavltree induct. (*recurse on t*)
  - solve_find. (*The t-is-Missing case*)
  - match goal with
      |- findResult ?x (_ ++ ^ ?y ++ _) =>
      case (compare_spec x y) end.
    (*Since we're deliberately trying NOT to use automatically generated
    hypothesis names, these inline match tacticals allow us to generate
    bindings based on patterns, and use them instead of hypothesis names.
    We'll also occasionally use argument names as well, although even that
    isn't necessary, as shown here.  Note how the content indexes provide a
    very nice way to specify patterns that are visually obvious.  Also, these
    matches will be somewhat more informative than if we had used hypothesis
    names directly, as it gives an indication of why a particular choice was
    made.  Here, the induction above exposed (because it was the datum at the
    root) some new element in the contents index of the conclusion,
    corresponding to the root datum of the inducted-on tree - so the obvious
    thing to do is compare it to our input element.*)
    all:[> (idtac + onhead findResult destr); solve_find..].
    (*The above solves all 3 cases via backtracking.  The "idtac" part is for
    when no recursion is necessary, while the "onhead findResult destr" does
    recursion - either into the left or right child (onhead has as many
    successes as there are hyps with that head type identifier).  We
    encapsulate this in a [> ..] form only for performance reasons - it is
    about 30X faster inside [> ..] in Coq 8.5beta3.  I know not why.*)
Qed.
(*Why end with Qed instead of Defined?  Ending a function definition with
Defined in Coq allows that function to be "unfolded" in later proofs, while
Qed does not.  Such unfolding makes those other proofs dependent on the
particulars of the implementations of the unfolded functions.  Which is
unmodular with a capital DON'T!  Except for the most trivial functions which
are really just abbreviations for their trivial bodies.  Furthermore,
unfolding large proof terms (and even the proof term of a function as small as
find is pretty large - do "Print find." to see it) in proofs will just make
those proofs really, really hard.  Also, one of the points to specifying the
function so precisely in its signature is that all info any usage needs is
available via the signature - so if you think you need to unfold it, that
really just indicates that maybe there's not enough info in the signature.
Also, Coq has the ability to asynchronously prove Qed-ended functions, but not
Defined-ended functions.

By the way - the sheer size and complexity of the proof terms for these
functions, which is partially due to the use of very-dependent types and
partially just because they're complex functions (not so much find, but wait
until insert and delete), also indicates that we're much better off defining
them using proof mode than if we tried to define them by providing a direct
Gallina term ("Definition :=" style).  Why do we get a big savings of effort
in proof mode?  Because of the tactics.  Some of them do a huge amount of
heavy lifting for filling in that proof term.  Even the built-in ones, like
inversion, provide lots of scaffolding in the proof term for dependent types -
that you could write yourself, but wouldn't want to.  The decision procedure
tactics encapsulate large amounts of mathematical reasoning ability.  The
proof search tactics scan through large spaces of possible programs/proofs to
find solutions.*)

(*Recursive Extraction find.*)
(*Without the Section around everything, find extracts to this:

--prelude stuff - ignore the warnings--

type wavltree =
| Missing
| Node of bool * wavltree * a * wavltree

type findResult =
| Found
| NotFound

(** val find : a -> wavltree -> findResult **)

let rec find x = function
| Missing -> NotFound
| Node (ug, lc, d, rc) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x lc
   | CompGtT -> find x rc)
 *)

(* Adding the Section adds an 'a arg to types and an ordA arg to functions -
representing the typeclass of elements.  But, things are easier to read
without those artifacts.  Note how nice a job the erasure did.*)

Ltac wavl_missing :=
(*A tactic that solves goals wanting a missing wavltree.  Now, we'll start
using that advanced tactic boom (which builds in bang) to solve equations
involving gaps and ranks when we don't know in advance whether those equations
involve unknowns (evars) or not.  Boom is not much more costly than bang - so
we really could have just used boom everywhere.*)
  eapply Missing; [boom..].

Ltac xinv H := 
(*A convenient inversion tactic, for use in cases where we know we will need
only the contents of the wavltree being inverted, not that wavltree itself.*)
     simple inversion H; [clear H; dintros; try boom..].

Definition setgap`(t : wavltree k ig lg rg f)(g : bool) : wavltree k #g lg rg f.
(* The setgap function alters just the gap of a non-missing wavltree.  This is
a case where we see that our imaginary gap on a missing wavltree allows for an
easier function specification and proof.  Another reason for wavltree having
so many type parameters - it is easier to write functions like setgap without
having to show that the only way the output wavltree differs from the input
tree is by gap.  To show that completely would be a bit more difficult (but it
could be done - we'd have to construct an equality predicate on wavltrees) -
but the type parameters and content type index us to show this sufficiently
for all use cases we care about.  Note that the only change in type parameters
and index occurring here is top-level the gap arg.  This becomes important
later, as we will encounter cases of wavltrees where the child gaps (lg and
rg) are crucial to the proof - so preserving them is necessary.*)
Proof.
  xinv t.
  - wavl_missing.
  - eapply Node.
    (*Since we're just changing the gap, we expect all of the subgoals to be
    easily solvable - and they are.  Note that we could use boom for the
    equations - using reflexivity here just demonstrates that we do get the
    ease we anticipate. *)
    all:try reflexivity; eassumption.
Qed.

Definition getgap`(t : wavltree k eg lg rg f) : { g | f<>[] -> #g=eg}.
(* To go with setgap, we would like a getgap function.  One might think that,
because the gap is a type parameter on every wavltree, we don't need a
function to retrieve it.  However, that gap type parameter is erased - meaning
it isn't present at runtime.  Since we want the actual unerased gap value, we
have to provide some runtime way to get at it.  Note as well that this means
we won't have an unerased gap value for missing wavltrees - and that is
reflect in the dependently-typed result for getgap. *)
Proof.
  xinv t.
  - econstructor;bang.
  - econstructor;bang.
(*We're left with a single bool goal.  It actually corresponds to the fact
that we don't care what value is returned in the missing case.  We can pick
one - so we'll choose false:*)
Grab Existential Variables.
  exact false.
Qed.

Definition gofis`(t : wavltree k g lg rg f)(ug : bool) : {k<>#(-1) /\ #ug=g}
                                                       + {k=#(-1) \/ #ug<>g}.
(*gofis - which means "gap-of-is" - is roughly a combination of isMissing and
getgap.  The meaning of "gofis t g" is "if t is not missing, is its gap g?" -
so it lumps together missing cases and non-g-gap cases.  We don't need this,
it just saves us an extra function call.*)
Proof.
  xinv t.
  (*Only one subgoal - which means xinv took care of the missing case for
  us.*)
  match goal with
    |- context[# ?B1 = # ?B2] => compare B1 B2 end.
  all:constructor;bang.
Qed.

Ltac wavl_assumption :=
(*Our first complicated tactic.  This is for solving wavltree goals when we
know that some wavltree assumption, suitably modified, will work.  The
acceptable modification is to the gap, and to the associativity of the
contents.  We could write this using the reassoc tactic to try all different
associativities of the contents, but it is faster to do things this way (less
backtracking).  The reassoc tactic is necessary when constructing a wavltree,
because the associativity of the contents forces a particular root.  Here,
since we're not constructing anything new, we don't care.  So, instead of
reassoc, we just do a replace, and solve the induced equality on contents by
un-associating (flattening) both sides.  Then, we use the "force exact" tactic
(utils.v) - which is used like exact, but creates equality subgoals for not
identical type parameters - and solve all resulting equalities with boom.*)
  (idtac + eapply setgap); (*try without setgap, then with if needed*)
  multimatch goal with
    H : wavltree _ _ _ _ ?F |- wavltree _ _ _ _ ?F' =>
    replace F' with F by (rewrite ?Eapp_assoc; reflexivity);
    force exact H;
    [boom..]
  end.

Ltac solve_wavl :=
(*This mutually recursive tactic, solve_wavl, can be used to solve any
wavltree that is solvable without additional case analysis (meaning, without
inverting existing wavltrees, or destructing gaps).  Note - if we didn't have
the contents as an index on the wavltree type family, the mutual recursion
between solve_wavl and wavl_construction might get into an endless loop.  The
contents index stops it because it induces "eapply Node" to destruct the
contents by pattern unification, instead of semantically.  In other words, an
arbitrary F : EL can be decomposed semantically forever, because we have no
idea how much it contains; but LF ++ ^x ++ RF can only be decomposed by
pattern unification once - we then get two child wavltrees with LF and RF as
contents, and eapply Node will fail vs. those - even though they may have
contents.  We'll thus require inversion of wavltrees to go from a single
variable contents field to something that eapply Node works on.  In theory,
indexes aren't even necessary in Coq (except for one in eq) - we could just
use type parameters and equalities - but indexes, including those that have
some "green slime" (functions, such as Eapp) , can make things easier if used
judiciously.*)
  dintros;
  (wavl_missing + wavl_assumption + wavl_construction)
with wavl_construction :=
  reassoc;
  eapply Node;
  (*eapply does not produce visible subgoals that correspond to implicit
  arguments or arguments that are solvable through unification elsewhere.
  Hence, we don't get visible subgoals for ug or d, even though those weren't
  declared implicit - one for ug is created, but shelved, as ug is solved when
  equg is solved - d is solved by the unification on the contents index, and
  so no subgoal is created for it.  We could use simple refine instead of
  eapply to bypass this automatic shelving and get something perhaps a bit
  more predictable - but we would end up trying to not solve those extra goals
  directly anyway in this case. *)
  [boom (*equg*)
  |boom (*eqlk*)
  |solve_wavl (*lc*)
  |boom (*eqrk*)
  |solve_wavl (*rc*)
  |ss (*s*)
  |boom (*leaf*)
  ].

(*The next two functions, rot1 and rot2, are rotations for insert - they are
abstracted out just for illustration purposes.  Their signatures were found by
first trying to solve insert directly - and looking for subgoals where the
existing wavltrees were obviously too dissimilar in rank (off by >1, such that
gap adjustments can't be used to make them into suitable siblings) to allow
for direct solution by solve_wavl.  We have other tactics that are not shown
here (rsimp, primarily) - they simplify goals but do not alter or solve them
in any way - and these were used to make it easier to spot when the ranks
became too dissimilar.*)

Definition rot1
           `(lt : wavltree k #false llg lrg lf)
           (x : A)
           `(rt : wavltree (k #- #2) #true rlg rrg rf)
           (gne : llg <> lrg)
           (s : Esorted (lf++^x++rf))
  : forall g, wavltree k #g #false #false (lf++^x++rf).
Proof.
  xinv lt.
  match goal with
  | W:wavltree _ ?G _ _ ?F, _:Esorted ((_ ++ _ ++ ?F) ++ ^x ++ rf) |- _ =>
    pose G as Egap; (*name this for use below*)
    xinv W
  end.
  - solve_wavl.
  - match get_value Egap with # ?gap => case_eq gap end.
    (*The solve_wavl tactic, and later ones built on it, are going to take
    some time when doing wavl_construction, as there are many different
    possible constructions of wavltrees to search through.  It's certainly
    possible to build some more intelligence into the searches so that they
    either avoid impossible cases or prioritize more likely cases first - but
    we won't do that so as to keep these tactics simple.  The worst cases of
    proof search we will encounter (in the delete rotations) are approaching
    10 minutes on a 2.5GHz Intel Core i5-2450M per search. *)
    + solve_wavl.
    + solve_wavl.
Qed.

Definition rot2
           `(lt : wavltree (k #- #2) #true llg lrg lf)
           (x : A)
           `(rt : wavltree k #false rlg rrg rf)
           (gne : rlg <> rrg)
           (s : Esorted (lf++^x++rf))
  : forall g, wavltree k #g #false #false (lf++^x++rf).
Proof.
  xinv rt.
  match goal with
  | W:wavltree _ ?G _ _ ?F, _:Esorted (lf ++ ^x ++ (?F ++ _ ++ _)) |- _ =>
    pose G as Egap;
    xinv W
  end.
  - solve_wavl.
  - match get_value Egap with # ?gap => case_eq gap end.
    + solve_wavl.
    + solve_wavl.
Qed.

(*Note: we could build a tactic that would solve rot1 and rot2 in a single
invocation - by having the tactic use backtracking proof search to try
inversion on existing wavltrees and destruction on existing unerased gaps.
This was done as an experiment - and it worked - but the tactic took more than
20 minutes to run.  One could envision a smarter variant that would make
better guesses about which wavltrees to try to invert first (the ones with
higher rank) and so on to speed things up.  Certainly, future versions of Coq
might have parallel proof search capability - that would help as well.  But,
it isn't too hard for a human to figure out what case analysis should be tried
at each point.  And, there are many judgment calls - for example: is it better
to invert a wavltree or call isMissing on it? *)

Ltac use_rot :=
(*a tactic for using those rotation functions - note that we don't use
solve_wavl for the lt and rt arguments, as we expect the arguments to be
available as hypotheses in the calling context.  The whole point to
abstracting out the rotation functions is so that their arguments don't need
construction, anyway.*)
  reassoc;
  (eapply rot1 + eapply rot2);
  (*eapply solves x by unification on the contents pattern itself*)
  [wavl_assumption (*lt*)
  |wavl_assumption (*rt*)
  |boom (*gne*)
  |ss (*s*)
  ].

Optimize Heap.

(* For the insert function, we will separate the result type into two parts.
The first level, insertResult, should be pretty obvious by now.  The second
level, insertedHow, shows the possible relationships that insert can produce
among the input and output gaps and ranks.  It was found by trial-and-error.
In other words, even if one has insufficient info on how the algorithm should
behave, attempts at proofs may help fill in the blanks.  The reason for
separating insertedHow from insertResult is so that we can solve one separate
from the other - which just amounts to saying that we end up with a faster
proof search (less backtracking). *)

Inductive insertedHow(ki ko : EZ)(gi go lgo rgo : EB)(f : EL) : Set :=
| ISameK : ko=ki -> f<>[] -> go=gi ->
           insertedHow ki ko gi go lgo rgo f
| IWasMissing : ki=#(-1) -> ko=#0 -> f=[] -> go=#false ->
                insertedHow ki ko gi go lgo rgo f
| IHigherK : ko=ki #+ #1 -> lgo<>rgo -> f<>[] -> go=#false ->
             insertedHow ki ko gi go lgo rgo f.

Inductive insertResult(x: A)(k : EZ)(g lg rg : EB) : EL -> Set :=
| FoundByInsert{fl fr} : insertResult x k g lg rg (fl++^x++fr)
| Inserted{ko go lgo rgo fl fr}
          (t : wavltree ko go lgo rgo (fl++^x++fr))
          (i : insertedHow k ko g go lgo rgo (fl++fr))
  : insertResult x k g lg rg (fl++fr).

Ltac solve_wavl2 :=
(*We'll now construct a tactic for solving inserts - it will incorporate the
original solve_wavl, but add the new use_rot tactic for trying rotations - and
try these first as there are only 2 alternatives*)
  use_rot + solve_wavl.

Ltac solve_insert :=
(*The full tactic has to do the standard things at its beginning (dintros,
reassoc), and solve the insertedHow part as well if it uses the Inserted
ctor.*)
  dintros;
  reassoc;
  (eapply FoundByInsert +
   (eapply Inserted;[solve_wavl2|econstructor;[solve[fnenil|boom]..]])).

Ltac unerase_gaps :=
(*We could just use gofis or inversion to find real (unerased) gaps against
which to examine cases, and then have to handle the missing cases.  Instead,
it is possible at various times that the gaps we see in the wavltree type args
are really already unerasable - because we can prove those wavltrees aren't
missing.  This tactic does just that - it examines each wavltree in the proof
context and attempts to prove that its not missing - and if so, then getgap
can be used effectively.  It doesn't matter if we call getgap and then don't
use the result - as such unused calls will not appear in the extracted code.
The nice thing about tactics like this is they allow one to find opportunities
during interactive proof.  It would be more accurate to call this tactic
show_unerasable_gaps, but that's too long.*)
  let f H :=
      try
        lazymatch type of H with
          wavltree _ ?G _ _ _ =>
          is_var G;
          case (getgap H);
          let X:=fresh in
          let G':=fresh in
          intros G' X;
          first [specialize (X ltac:(assumption||fnenil))
                |specialize (X (wavlfnenil H ltac:(bang)))];
          rewrite <-X in *;
          clear X G;
          rename G' into G
        end in
  hyps => loop f.

Definition insert(x : A)`(t : wavltree k g lg rg f) : insertResult x k g lg rg f.
Proof.
  onhead wavltree induct.
  - change ([]:EL) with ([]++[]:EL).
    (*OK - so there is a downside to depending on unification for the contents
    index - it can't tell that semantically identical contents are the same.
    In this case, it wants an _ ++ _ form to unify with, and [] doesn't
    suffice - so we have to change it to the semantically identical []++[] to
    make it work.  We could have built this into solve_insert - but it's only
    needed at this one spot. *)
    solve_insert.
  - match goal with
      |- insertResult ?X _ _ _ _ (_ ++ ^ ?Y ++ _) =>
      case (compare_spec X Y) end.
    + solve_insert.
    + match goal with
        H:insertResult _ _ _ _ _ ?F |-
        lt ?X ?Y -> insertResult _ _ _ _ _ (?F ++ ^ ?Y ++ _) => xinv H end.
      * solve_insert.
      * onhead insertedHow xinv.
        -- solve_insert.
        -- match goal with
             R : wavltree _ _ _ _ ?RF
             |- insertResult _ _ _ _ _ (_ ++ _ ++ ?RF) =>
             case (isMissing R) end.
           ++ solve_insert.
           ++ solve_insert.
        -- unerase_gaps.
           match goal with
           | _ : wavltree _ # ?G _ _ ?LF,
             _ : Esorted (?LF ++ _ ++ _) |- _ =>
             case_eq G end.
           ++ solve_insert.
           ++ match goal with
              | R : wavltree _ _ _ _ ?RF,
                _ : Esorted (_ ++ _ ++ ?RF) |- _ =>
                case (gofis R false) end.
              ** solve_insert.
              ** solve_insert.
    + match goal with
        H:insertResult _ _ _ _ _ ?F |-
        lt ?Y ?X -> insertResult _ _ _ _ _ (_ ++ ^ ?Y ++ ?F) => xinv H end.
      * solve_insert.
      * onhead insertedHow xinv.
        -- solve_insert.
        -- match goal with
             L : wavltree _ _ _ _ ?LF,
             _ : Esorted (?LF ++ _ ++ _ ++ _) |- _ =>
             case (isMissing L) end.
           ++ solve_insert.
           ++ solve_insert.
        -- unerase_gaps.
           match goal with
           | _ : wavltree _ # ?G _ _ ?RF,
             _ : Esorted (_ ++ _ ++ ?RF) |- _ =>
             case_eq G end.
           ++ solve_insert.
           ++ match goal with
              | L : wavltree _ _ _ _ ?LF,
                _ : Esorted (?LF ++ _ ++ _) |- _ =>
                case (gofis L false) end.
              ** solve_insert.
              ** solve_insert.
Qed.

(*In the extracted code for insert, note that every call to a rotation is
paired with ISameK, and every recursive call that returns ISameK also produces
an ISameK result.  This implies that at most one rotation is needed for
insertion into a weak-AVL tree.  We'll see later that this is also true for
deletion.*)

Optimize Heap.

(**********************************************************************)

(*We turn our attention now to delete - which needs some of its own
preliminary functions.  The first is tryLowering - which takes a wavltree and
attempts to reduce its rank by 1 basically for free - just by removing the
gaps between its root and the root's children - effectively lowering just the
root's rank.  Obviously, this is only possible if both of the root's children
have gaps.

Why would we anticipate needing tryLowering?  We actually did not.  Instead,
during the proofs of the delete-specific rotation functions (drot1 and drot2,
coming up shortly), it became obvious that we could only rotate trees if we
knew something about their child gaps.  A little thought about this, and
tryLowering becomes a fairly obvious function to attempt - as it will either
make a rotation unnecessary, or reveal just the info about the child gaps
needed to get the rotations to work.

Again, we prefer a function-specific dependent return type to express the
result: *)

Inductive tryLoweringResult`(t : wavltree k g lg rg f) : Set :=
| TLtooLow(p : lg=#false \/ rg=#false) (*at least one child has no gap*)
| TLlowered(p: lg=#true /\ rg=#true)(t': wavltree (k #- #1) g #false #false f).

Ltac solve_tl :=
(*Now, as before, we develop a specific tactic to solve tryLowering's subgoals
- it should by now have a familiar look to it.  Note that reassoc isn't
needed, because we won't need to refer to the tree's contents in any way. *)
  dintros;
  ((eapply TLtooLow; boom) +
   (eapply TLlowered; [boom|solve_wavl])).

Definition tryLowering`(t : wavltree k g lg rg f) : tryLoweringResult t.
Proof.
  simple inversion t.
  - solve_tl.
  - dintros.
    match goal with
    | L : wavltree _ _ _ _ ?LF, _ : Esorted (?LF ++ _ ++ _) |- _ =>
      case (gofis L true)
    end.
    + dintros.
      match goal with
      | R : wavltree _ _ _ _ ?RF, _ : Esorted (_ ++ _ ++ ?RF) |- _ =>
        case (gofis R true)
      end.
      * solve_tl.
      * solve_tl.
    + solve_tl.
Qed.

(* For the remaining delete functions, the dependent return types share common
elements.  We will separate the return types into three levels, two of which
will be repeatedly used.  The first level is deletedHow - which, like
insertedHow, carries the relationships between input and output gaps and
ranks.  It turns out that in this respect, delete is a bit easier than insert
- there are just two choices of relationship, and they are quite easily
anticipated: DSameK is if the delete does not reduce the rank of the
deleted-from tree, and DLowerK is when it does (by 1).  In both cases, we get
to choose the gap of the returned deleted-from tree - so we prefer the gap
that most likely would leave things as they were - same as the input gap for
DSameK, and true for DLowerK (so that if the input gap was false, the output
subtree would still fit in place of the input one). *)

Inductive deletedHow(ki ko : EZ)(gi go : EB) : Set :=
| DSameK(keq : ko=ki)(eg : go=gi)
| DLowerK(keq :  ki=ko #+ #1)(eg: go=#true).

(*The second level of dependent return type for delete functions is delpair -
which is really just a dependent pair (if you don't bother to count the
implicit args).  The reason for making it a separate return type is due to is
commonality among the remaining types below, and as a convenient output type
for the delete rotation functions.*)

Inductive delpair(k : EZ)(g : EB)(f : EL) : Set :=
| Delout`(t : wavltree ko go lgo rgo f)(d : deletedHow k ko g go).

Ltac solve_delpair :=
(*Since we'll be seeing a lot of goals asking for a delpair, we'll construct a
solver tactic for it in the usual way.  Why doesn't solve_delpair call
reassoc?  It's a bit subtler than the reason for solve_tl: we obviously do
care when deleting about contents, but by the time we need a delpair, all
reassessing must have already been done.  We can see that by the fact that we
don't even bother to make the contents a type index of delpair - it's a type
parameter instead, and so doesn't filter out potential unification's by
pattern.  Said another way, delpair does not itself demonstrate that we've
altered the contents of a tree in some way vs. some other way - as it has only
one constructor. *)
  dintros;
  eapply Delout;
  [|constructor;[boom..]]; (*solve deletedHow first, as it is most limiting*)
  solve_wavl.

(*The deletion rotations.  Note their similarity to the insertion rotations.
They have subtle differences.  One is that the "gne" arg of the insert
rotations has been replaced by the "tltl" arg - which stands for "tryLowering
returned 'too low'" - and is precisely the info we get back from a failed
tryLowering attempt on the higher input tree (t2).  The other is that we're
required to build an output tree (delpair's t) that is one rank level above
the higher input tree, not the same rank as the higher input tree as with the
insert rotations.  However, just as with the insert rotations, these delete
rotation functions were found by first trying to solve the delete function
alone, and then finding those subgoals where the mismatch in ranks between
available subtrees was too large - and abstracting out those cases.*)

Definition drot1
           `(t : wavltree (k #- #3) #true lgo rgo f)
           (d : A)
           `(t2 : wavltree (k #- #1) #false rlg rrg rf)
           (s : Esorted (f ++ ^ d ++ rf))
           (tltl : rlg = #false \/ rrg = #false)
  : forall ug, delpair k #ug (f ++ ^d ++ rf).
Proof.
  xinv t2.
  match goal with
  | W:wavltree _ _ _ _ ?F, _:Esorted(_ ++ _ ++ ?F ++ _ ++ _) |- _ =>
    simple inversion W end.
  - solve_delpair.
  - match goal with
    | W:wavltree _ _ _ _ ?F, _:Esorted(_ ++ _ ++ _ ++ _ ++ ?F) |- _ =>
      case (gofis W false) end.
    + solve_delpair.
    + solve_delpair.
Qed.

Optimize Heap.

Definition drot2
           `(t2 : wavltree (k #- #1) #false llg lrg lf)
           (d : A)
           `(t : wavltree (k #- #3) #true lgo rgo f)
           (s : Esorted (lf ++ ^ d ++ f))
           (tltl : llg = #false \/ lrg = #false)
  : forall ug, delpair k #ug (lf ++ ^d ++ f).
Proof.
  xinv t2.
  match goal with
  | W:wavltree _ _ _ _ ?F, _:Esorted((_ ++ _ ++ ?F) ++ _ ++ _) |- _ =>
    simple inversion W end.
  - solve_delpair.
  - match goal with
      | W:wavltree _ _ _ _ ?F, _:Esorted((?F ++ _ ++ _) ++ _ ++ _) |- _ =>
        case (gofis W false) end.
    + solve_delpair.
    + solve_delpair.
Qed.

(* One important point about the above delete rotation functions - they always
return DSameK in their deletedHow field (which you can see by extracting
them).  This is important for the performance of deletion of weak-AVL trees -
and when combined with the fact that delete/delmin/delmax always return DSameK
in cases when their recursive calls returned DSameK, means that deletion in
weak-AVL trees, like insertion, performs at most one rotation.  We could have
solved the above delete rotations functions in different ways, such that some
of their branches return DLowerK, but didn't need to do that - and the lucky
fact that we placed DSameK as the first constructor of deletedHow with DLowerK
second forced the proof searches to try all DSameK combinations first.  If we
want to enforce this fact, we could add another type parameter to delpair like
so:

Inductive delpair(k : EZ)(g eqks: EB)(f : EL) : Set := 
| Delout`(t : wavltree ko go lgo rgo f)(d : deletedHow k ko g go)
         (require_eqks : eqks=#true -> ko=k).

and specified in the signatures of the delete rotations that eqks is #true,
while allowing to have any value in the other delete functions.  Or, make ko
itself a type parameter, and force ko=k in the delete rotation usage of
delpair, but not elsewhere.  Etc.*)

Optimize Heap.

Ltac use_drot :=
(*Build up a solve_delpair2 tactic similarly to how we built up a solve_wavl2
tactic for insert:*)
  dintros;
  reassoc;
  (eapply drot1 + eapply drot2);
  [wavl_assumption|wavl_assumption|ss|assumption].

Ltac solve_delpair2 := use_drot + solve_delpair.

(*We still have 2 more functions to define before delete - really, only one is
needed, but we'll define both.  These are delmin (delete the minimum element
of a tree) and delmax (delete the maximum element of a tree).  If you are
familiar with the way similar algorithms (AVL and red-black trees, for
example) are implement, then these should not surprise you.  However, again,
if we first attempted delete, we would arrive at a point where we removed the
desired element, but didn't have a replacement for it.  It doesn't take much
thought at that point to realize that a perfect replacement can be had by
either deleting the maximum element from the lesser subtree or the minimum
element from the greater subtree.  We'll do one or the other based on which
subtree has higher rank. *)

Inductive delminResult(k : EZ)(g : EB) : EL -> Set :=
| NoMin : delminResult k g []
| MinDeleted(min : A){f}(dr : delpair k g f)
  : delminResult k g (^min++f).

Ltac solve_delmin :=
  dintros;
  reassoc;
  try rewrite Eapp_nil_l;
  (*Why is this "try rewrite Eapp_nil_l" here?  This is again a way to
  compensate for the shortcomings of treating contents as a type index instead
  of a type parameter - Coq unifies/pattern matches instead of giving us an
  EL-equation to solve.  So, we have to anticipate cases like "delminResult k
  g ([]++^x++f)", which would not unify with MinDeleted on its own.  The
  rewrite rule Eapp_nil_l removes nils on the left of erased lists.*)
  (eapply NoMin +
   (eapply MinDeleted; solve_delpair2)).

Definition delmin`(t : wavltree k g lg rg f) : delminResult k g f.
Proof.
  induction t.
  - solve_delmin.
  - match goal with
    | LH : delminResult _ _ ?LF, RH : delminResult _ _ ?RF
      |- delminResult _ _ (?LF ++ _ ++ ?RF) =>
      (*choose the proper recursive call to make:*)
      clear RH; inversion LH; subst end.
    + solve_delmin.
    + (*We need to expose the info we just got from the recursive call above*)
      onhead delpair destr.
      onhead deletedHow destr; subst.
      * solve_delmin.
      * match goal with
        | W : wavltree _ _ _ _ ?RF |- delminResult _ _ (_ ++ _ ++ ?RF) =>
        case (gofis W false) end.
        -- dintros.
           match goal with
           | W : wavltree _ _ _ _ ?LF |- delminResult _ _ (?LF ++ _ ++ _) =>
           case (gofis W true) end.
           ++ dintros.
              match goal with
              | W : wavltree _ _ _ _ ?RF |- delminResult _ _ (_ ++ _ ++ ?RF) =>
              case (tryLowering W) end.
              ** solve_delmin.
              ** solve_delmin.
           ++ solve_delmin.
        -- unerase_gaps.
           (*Why use unerase_gaps, when we're not going to do any
           case-analysis on the resulting unerased gaps?  The reason has to do
           with the fact that, within wavl_assumption, we built-in an attempt
           at using setgap, but we never built-in a way to get gaps from other
           wavltrees.  All that the setgap could do is use existing bools
           (which are all previously unerased gaps) in the context.  One might
           think we could have put a call to unerase_gaps into wavl_assumption
           - but there are overly conservative rules in Coq about what values
           are allowable instantiations for evars, and waiting until
           wavl_assumption was called before unerasing more gaps would fall
           afoul of those rules.  We could instead put a call to unerase_gaps
           at the top of solve_delmin - that would work for just this one
           spot, but slow all of the others down for no good reason.*)
           solve_delmin.
Qed.

Optimize Heap.

(*delmax is a mirror image of delmin*)
Inductive delmaxResult(k : EZ)(g : EB) : EL -> Set :=
| NoMax : delmaxResult k g []
| MaxDeleted(max : A){f}(dr : delpair k g f)
  : delmaxResult k g (f++^max).

Ltac solve_delmax :=
  dintros;
  reassoc;
  try rewrite Eapp_nil_r;
  (eapply NoMax +
   (eapply MaxDeleted; solve_delpair2)).

Definition delmax`(t : wavltree k g lg rg f) : delmaxResult k g f.
Proof.
  induction t.
  - solve_delmax.
  - match goal with
    | LH : delmaxResult _ _ ?LF, RH : delmaxResult _ _ ?RF
      |- delmaxResult _ _ (?LF ++ _ ++ ?RF) =>
      clear LH; inversion RH; subst end.
    + solve_delmax.
    + onhead delpair destr.
      onhead deletedHow destr; subst.
      * solve_delmax.
      * match goal with
        | W : wavltree _ _ _ _ ?LF |- delmaxResult _ _ (?LF ++ _ ++ _) =>
        case (gofis W false) end.
        -- dintros.
           match goal with
           | W : wavltree _ _ _ _ ?RF |- delmaxResult _ _ (_ ++ _ ++ ?RF) =>
           case (gofis W true) end.
           ++ dintros.
              match goal with
              | W : wavltree _ _ _ _ ?LF |- delmaxResult _ _ (?LF ++ _ ++ _) =>
              case (tryLowering W) end.
              ** solve_delmax.
              ** solve_delmax.
           ++ solve_delmax.
        -- unerase_gaps.
           solve_delmax.
Qed.

Optimize Heap.

(*Finally, delete.  No surprises here.*)

Inductive deleteResult(x : A)(k : EZ)(g : EB) : EL -> Set :=
| Deleted{f1 f2}(dr : delpair k g (f1++f2))
  : deleteResult x k g (f1++^x++f2)
| DNotFound{f} : ENotIn x f -> deleteResult x k g f.

Ltac solve_delete :=
  dintros;
  reassoc;
  ((eapply Deleted;
   (idtac + (rewrite Eapp_nil_r || rewrite Eapp_nil_l));
   solve_delpair2)
   + (eapply DNotFound; ss)).

Definition delete(x : A)`(t : wavltree k g lg rg f) : deleteResult x k g f.
Proof.
  induction t.
  - solve_delete.
  - match goal with
      Y:A |- deleteResult ?X _ _ (_ ++ ^ ?Y ++ _) =>
      case (compare_spec X Y) end.
    + dintros.
      match goal with
      | W : wavltree _ _ _ _ ?RF |- deleteResult _ _ _ (_ ++ _ ++ ?RF) =>
      case (gofis W false) end.
      * dintros.
        match goal with
        | W : wavltree _ _ _ _ ?RF |- deleteResult _ _ _ (_ ++ _ ++ ?RF) =>
          destruct (delmin W) end.
        -- solve_delete.
        -- onhead delpair destr.
           onhead deletedHow destr; subst.
           ** solve_delete.
           ** match goal with
              | W : wavltree _ _ _ _ ?LF |- deleteResult _ _ _ (?LF ++ _ ++ _ ++ _) =>
              case (isMissing W) end.
              --- solve_delete.
              --- solve_delete.
      * dintros.
        match goal with
        | W : wavltree _ _ _ _ ?LF |- deleteResult _ _ _ (?LF ++ _ ++ _) =>
          destruct (delmax W) end.
        -- solve_delete.
        -- onhead delpair destr.
           onhead deletedHow destr; subst.
           ++ solve_delete.
           ++ unerase_gaps.
              solve_delete.
    + match goal with
      | LH : deleteResult _ _ _ ?LF, RH : deleteResult _ _ _ ?RF
       |- lt ?X ?Y -> deleteResult _ _ _ (?LF ++ ^ ?Y ++ ?RF) =>
       clear RH; inversion LH; dintros end.
      * onhead delpair destr.
        onhead deletedHow destr; subst.
        -- solve_delete.
        -- unerase_gaps.
           match goal with
           | _ : wavltree _ # ?LG _ _ ?F
             |- deleteResult _ _ _ (?F ++ _ ++ _) =>
           case_eq LG end.
           ++ dintros.
              unerase_gaps.
              match goal with
              | _ : wavltree _ # ?RG _ _ ?RF |- deleteResult _ _ _ (_ ++ _ ++ ?RF) =>
              case_eq RG end.
              ** solve_delete.
              ** dintros.
                 match goal with
                 | W : wavltree _ _ _ _ ?RF |- deleteResult _ _ _ (_ ++ _ ++ ?RF) =>
                 case (tryLowering W) end.
                 --- solve_delete.
                 --- solve_delete.
          ++ dintros.
             match goal with
             | W : wavltree _ _ _ _ ?RF |- deleteResult _ _ _ (_ ++ _ ++ ?RF) =>
             case (isMissing W) end.
             ** solve_delete.
             ** solve_delete.
      * solve_delete.
    + match goal with
      | LH : deleteResult _ _ _ ?LF, RH : deleteResult _ _ _ ?RF
       |- lt ?Y ?X -> deleteResult _ _ _ (?LF ++ ^ ?Y ++ ?RF) =>
       clear LH; inversion RH; dintros end.
      * onhead delpair destr.
        onhead deletedHow destr; subst.
        -- solve_delete.
        -- unerase_gaps.
           match goal with
           | _ : wavltree _ # ?RG _ _ ?RF
             |- deleteResult _ _ _ (_ ++ _ ++ ?RF) =>
           case_eq RG end.
           ++ dintros.
              unerase_gaps.
              match goal with
              | _ : wavltree _ # ?LG _ _ ?LF
                |- deleteResult _ _ _ (?LF ++ _ ++ _ ++ _ ++ _) =>
              case_eq LG  end.
              ** solve_delete.
              ** dintros.
                 match goal with
                 | W : wavltree _ _ _ _ ?LF
                   |- deleteResult _ _ _ (?LF ++ _ ++ _ ++ _ ++ _) =>
                 case (tryLowering W) end.
                 --- solve_delete.
                 --- solve_delete.
           ++ dintros.
              match goal with
              | W : wavltree _ _ _ _ ?LF
                |- deleteResult _ _ _ (?LF ++ _ ++ _ ++ _ ++ _) =>
              case (isMissing W) end.
              ** solve_delete.
              ** solve_delete.
     * solve_delete.
Qed.

(* End Wavltree. *)

Set Printing Width 120.

(*This tells Coq that the delpair type can be represented during extraction by
the OCaml pair type:*)
Extract Inductive delpair => "( * )" [ "" ].

(*Somewhere in the boom tactic, a setgap usage is picking up "(negb true)" as
its value instead of "false".  Obviously, they're the same, but it would be
nice to figure out why this is happening.  Until then, we can just tell Coq to
inline calls to negb to remove the blemish: *)
Extraction Inline negb.

Extraction "wavl.ml" find insert delete.
