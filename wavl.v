
(*** Weak AVL Trees ***)

(*+ 
See "Rank-Balanced Trees" by Haeupler, Sen, Tarjan
[http://www.cs.princeton.edu/~sssix/papers/rb-trees-talg.pdf].
*)

(*! Coq proof style:

  - Define all but most trivial functions using proof mode.

  - Keep all but the most trivial functions opaque (via Qed), as their types
    should suffice for all usages, making unfolding unnecessary (unfolding is
    unmodular).

  - Do not depend on any non-argument hypotheses names.

  - Do not depend on hypothesis order.

  - Do not use intro patterns.

  - Target tactics to hyps based on their type and relationship to arguments,
    using projector-like tactic/notations for readability.

  - Do not use type indexes - use type parameters and equality fields instead.

  - Tailor simple solver tactics for each function definition.

  - Use brief tactic notations and proof bullets to improve proof structure
    readability.

 *)
Set Ltac Profiling.
Require Import mindless.elist.
Require Import mindless.ezbool.
Require Import mindless.utils.
Require Import mindless.hypiter.

Generalizable All Variables.

Set Default Goal Selector "all".

Context {A : Set}.

Context {ordA : Ordered A}.

Context {compare : A -> A -> comparison}.

Context {compare_spec : forall x y, CompareSpecT (eq x y) (lt x y) (lt y x) (compare x y)}.

(* trinary (eq, lt, gt) comparisons of A elements: *)
Notation "x =<> y" := (compare_spec x y) (at level 70, only parsing).

(*All type parameters will be in these three erasable types:*)
Notation EL := ##(list A).
Notation EZ := ##Z.
Notation EB := ##bool.
(*These types are sufficient for the specification of all relevant invariants
in the definitions that follow.  Furthermore, we have specialized tactics for
solving goals involving these types.  The tactic solve_sorted from
solve_sorted.v solves Esorted and ENotIn goals on ELs.  The tactics bang and
boom from ezbool.v solve equalities in EZ that include converted (using ^
prefix operator) EBs, and which (in the case of boom) may include evars
linking multiple goals.*)

(*E_scope has been defined so that erasable versions of operators in Z (+, -)
and list (++ and [_]) can be written directly, so that they resemble the
corresponding unerased operators.  The erasable operator itself (#) is then
only needed for constants and variables.*)
Open Scope E_scope.

(* Weak-AVL trees with rank k, parent gap pg, child gaps lg and rg (for left
and right children respectively) and contents c (as a flattened list of all
elements in sorted order).

The presence of a gap between a parent and child indicates that the rank of
the parent is 2 greater than that of the child.  The absence of a gap
indicates a rank difference of 1.

Each node contains fields g (gap : boolean), d (datum), lw (left subtree), and
rw (right subtree) as its only runtime (unerasable) fields.  The remaining
fields are all in Prop, and so will all be erased at Extraction.

Missing trees have (obviously) no runtime fields, but do have erasable fields
specifying that the contents are empty (c = []), that the rank is -1, and that
both missing subtree gaps should be considered false (this choice makes a few
things slightly easier, primarily tryLowering, but any choide could be 
accommodated - as well as leaving them to "float").

The formulation, specifically with regard to ranks, is intended to mirror the
formulation in "Rank-Balanced Trees" by Haeupler, Sen, Tarjan
[http://www.cs.princeton.edu/~sssix/papers/rb-trees-talg.pdf], specifically:

"A ranked binary tree is a binary tree each of whose nodes x has a
non-negative integer rank r(x). We adopt the convention that missing nodes
have rank −1. The rank of a ranked binary tree is the rank of its root. If x
is a node with parent p(x), the rank difference of x is r(p(x)) − r(x)."

and

"Weak AVL Rule: All rank differences are 1 or 2 and every leaf has rank 0."

and

"We can represent ranks in a wavl tree using one bit per node. The most
straightforward way to do this is to use the bit in a node to indicate whether
its rank difference is 1 or 2."

However, we use k for ranks instead of r.  We reserve r as a prefix to
indicate "right" (and l for "left").  The gap fields are the bit per node
indicators of rank difference.

Note that the leaf_rule field in Node corresponds to the requirement that
every leaf has rank 0, as it requires that a node with rank 1 must have at
least one child with no gap, hence at rank 0, hence not missing.  This
roundabout way of specifying the leaf rule makes use of the existing gap and
rank parameters, without requiring any additional parameters (such as a
boolean type parameter signifying if the subtree is missing or not).  We check
in section Check_Leaf_Rule below that the expected equivalence between rank 0
and leaves is enforced.*)
Inductive wavltree (k : EZ)(pg lg rg : EB)(c : EL) : Set :=
| Node(g : bool)(d : A)
      (_: #g = pg)
      `(_: c = lc++[d]++rc) 
      `(lw : wavltree (k - #1 - ^lg) lg llg lrg lc)
      `(rw : wavltree (k - #1 - ^rg) rg rlg rrg rc)
      (leaf_rule: k = #1 -> lg = #false \/ rg = #false)
      (_: Esorted c)
| Missing(_: c = [])(_: k = - #1)(_: lg = #false)(_: rg = #false).

(**********************************************************************)

(*Tactic notations to make the proofs more readable:*)

(*The only case analysis tactics we will use are ?? and ??_on.  The reason for
using a concise notation for case analysis tactics (and later also solver
tactics) is so that the structure of the function is easier to recognize in
the proof:*)
Tactic Notation "??" constr(H) :=
  (*use case_eq if H is a hyp with dependents, else case*)
  (tryif (is_var H; try (clear H; (*clear H fails if H as dependents*)
                         fail 1))
    then case_eq H
    else case H);
  dintros.

(*This "on" version is just used for recursive calls, as it removes the need
to "_" args that would be implicit in outside calls: *)
Tactic Notation "??" constr(H) "on" constr(H') :=
  case H with (1:=H'); dintros.

(*Projector-like tactic/notation combos to select hypotheses based on type and
relationship to the wavltree argument.  This enables the proofs to maintain
independence from both non-argument hypothesis naming and ordering while
retaining readability. *)

Tactic Notation "just" tactic1(tac) := let x := tac in exact x.

Ltac left_child w :=
  lazymatch type of w with
    wavltree _ _ _ _ (?C++[_]++_) =>
    lazymatch goal with
      L:wavltree _ _ _ _ C |- _ => L
    end
  end.

Notation "'left_child' w" := ltac:(just left_child w)
                                    (at level 199, no associativity, only parsing).

Ltac right_child w :=
  lazymatch type of w with
    wavltree _ _ _ _ (_++[_]++?C) =>
    lazymatch goal with
      R:wavltree _ _ _ _ C |- _ => R
    end
  end.

Notation "'right_child' w" := ltac:(just right_child w)
                                     (at level 199, no associativity, only parsing).

Ltac datum w :=
  lazymatch type of w with
    wavltree _ _ _ _ (_++[?D]++_) => D
  end.

Notation "'datum' w" := ltac:(just datum w)
                               (at level 199, no associativity, only parsing).

Ltac gap w :=
  lazymatch type of w with
    wavltree _ # ?G _ _ _ => G
  end.

Notation "'gap' w" := ltac:(just gap w)
                             (at level 199, no associativity, only parsing).

Notation "'pick' x" := ltac:(just pick x)
                             (at level 199, no associativity, only parsing).

(*We will denote solving tactics with ! and !!.  ! will always refer to the
bang tactic defined in ezbool.v, which will be the workhorse for solving goals
involving gaps and ranks.  The boom tactic, a more powerful version of bang,
which also solves interdependent goals involving shared evars, will be used
within later solver tactics.  !! will refer in each section to a solver tactic
specific to the proofs in that section.  The "[>..]" tactical is used to wrap
solver tactics so that they run faster over multiple goals.  This is because
Coq's backtracking search is a bit too conservative when it has global focus,
and this results in a loss of performance.  The [>..] tactical forces proof
search within it to have local focus over all subgoals.*)

Tactic Notation "!" := [>bang..].

(**********************************************************************)

Section Lemmas.

  (*Because we use Z (integers) for ranks, instead of nat, we need to prove a
  lower bound for ranks: *)
  Lemma wavl_min_rank`(w : wavltree k g lg rg c) : k >= - #1.
  Proof. induction w. !. Qed.

  (*Nodes, which have non-empty contents, must have non-negative ranks.*)
  Lemma wavl_node_min_rank`(w : wavltree k g lg rg c) : c <> [] -> k >= #0.
  Proof.
    ?? w.
    1: pose proof (wavl_min_rank (left_child w)). (*either child would work*)
    !.
  Qed.
  
  (*reverse implication of the above*)
  Lemma wavl_node_nonempty`(w : wavltree k g lg rg c) : k >= #0 -> c <> [] .
  Proof. ?? w. !. Qed.

  (*Two lemmas that are used to project the field equalities from Missings: *)
  Lemma missing_contents`(w : wavltree (- #1) g lg rg c) : c = [] .
  Proof.
    pose proof (wavl_node_min_rank w).
    ?? w. !.
  Qed.

  Lemma missing_rank`(w : wavltree k g lg rg []) : k = - #1.
  Proof.
    ?? w.
    - fnenil.
    - tauto.
  Qed.

  (*A projector for the Esorted field, used by ss_setup_tactic below.*)
  Lemma wavl_is_sorted`(w : wavltree k g lg rg c) : Esorted c.
  Proof.
    ?? w.
    - assumption.
    - repeat econstructor.
  Qed.

End Lemmas.

(*We use the above lemmas to augment the power of the primary solver tactics
bang (from ezbool.v) and solve_sorted (from solvesorted.v) by adding relevant
wavltree information to the proof context prior to attempting a solution.  The
bang_setup_tactic is already defined for use by bang, so we redefine it to
make use of the above lemmas: *)
Ltac bang_setup_tactic ::=
  let f H :=
      (lazymatch type of H with
       | wavltree _ _ _ _ _ =>
         (*it is important that wavl_min_rank is tried last (the rest of the
         order doesn't matter) because wavl_min_rank always works, but
         produces the least specific info*)
         first [apply missing_rank in H
               |apply wavl_node_min_rank in H; [|assumption||fnenil]
               |apply wavl_min_rank in H]
       | _ => idtac
       end) in
  allhyps_td f.

(*The solve_sorted tactic is defined over normal lists and NotIn, not EL or
ENotIn, and does not come equipped with its own setup tactic - so we both
define a setup tactic and a solver tactic that uses it, as well as calling
unerase (which alters a goal with a Prop conclusion so that all erasable types
are replaced by their base types):*)
Ltac ss_setup_tactic :=
  let f H := (try apply wavl_is_sorted in H) in
  allhyps_td f.

Ltac ss := ss_setup_tactic; unerase; solve[solve_sorted].

(*The unerase tactic, defined in erasable.v, can be thought of as transforming
the current goal such that all erasable data in its context becomes "normal"
data - the names of hypotheses are preserved, just their types are altered.
The result is that the formerly erased data becomes accessible to subsequent
tactics.  This is only possible if the conclusion is a Prop, as that ensures
that the current goal is "uninformative": it will not be involved in the
extracted program, hence the transformation from erasable to normal data is
legal.  However, unerase is able to do some minor things when the conclusion
is not a Prop, most notably transform some equalities of erased data to
equalities of normal data.*)

(**********************************************************************)

Section Check_Leaf_Rule.
  
  (*Check that the leaf_rule field in wavltree's Node constructor properly
  enforces the expected equivalence between rank 0 and leaves:*)

  Local Set Asymmetric Patterns.

  Local Definition is_leaf`(w : wavltree k g lg rg c) : bool :=
    match w with
    | Node _ _ _ _ _ _ _ _ (Missing _ _ _ _) _ _ (Missing _ _ _ _) _ _ => true
    | _ => false
    end.

  Local Ltac destruct_match :=
    match goal with |- context[match ?X with _ => _ end] => destruct X end.

  Local Lemma leaf_rule_works`(w : wavltree k g lg rg c) : k = #0 <-> is_leaf w = true.
  Proof.
    unfold is_leaf.
    repeat destruct_match.
    !.
  Qed.

  (*Note: this is a case of a non-proof-mode, non-Qed function (is_leaf) that
  is unfolded - an apparent violation of proof style.  But, it is only used to
  demonstrate that the leaf-rule works.*)

End Check_Leaf_Rule.

(**********************************************************************)

Section Find.

  (*A simple example: the find function.  We will tend to use the same
  procedure for all functions: define a Result type for the function, define a
  simple tailored solver tactic that uses backtracking proof search, use the
  tactic notation !! for this solver tactic, then define the function. *)

  Inductive findResult(x : A)(c : EL) : Set :=
  | Found`(_: c = lc++[x]++rc)
  | NotFound(_: ENotIn x c).

  Ltac solve_find :=
    dintros; (*does intros, decomposes conjunctions, and substs*)
    reassoc; (*see note below*)
    ((eapply Found; reflexivity) || (eapply NotFound; ss)).

  (*Note: the reassoc tactic, which is defined in elist.v, is a backtracking
  tactic where each success is a different rewrite of a list (EL) in the
  conclusion with distinct top-level assocativity.  We will later use reassoc as
  a way to force the associativity of the conclusion's contents parameter to
  guide proof search down different search paths corresponding to different
  placements of its root datum.*)

  Tactic Notation "!!" := [>solve_find..].

  Fixpoint find(x : A)`(w : wavltree k g lg rg c) : findResult x c.
  Proof.
    (*examine w*)?? w.
    - (*w is Node*)?? (x =<> (datum w)).
      + (*x=d*)!!.
      + (*x<d*)?? (find x) on (left_child w). !!.
      + (*x>d*)?? (find x) on (right_child w). !!.
    - (*w is Missing*)!!.
  Qed.

End Find.

(*Some auxiliary helper functions:*)

Section SetGap.

  Tactic Notation "!!" := [>econstructor; (reflexivity || eassumption)..].

  Definition setgap`(w : wavltree k ig lg rg c)(og : bool) : wavltree k #og lg rg c.
  Proof. ?? w. !!. Qed.

End SetGap.

Section GetGap.

  Tactic Notation "!!" := [>unshelve eexists; [eassumption || exact false | boom]..].

  Definition getgap`(w : wavltree k g lg rg c) : { g' | c <> [] -> #g' = g}.
  Proof. ?? w. !!. Qed.

  Definition getgap2`(w : wavltree k g lg rg c) : { g' | k >= #0 -> #g' = g}.
  Proof. ?? w. !!. Qed. (*isn't used*)
  
End GetGap.

Section IsGap.

  Tactic Notation "!!" := [>constructor; boom..].

  Notation "x ?= y" := (Bool.bool_dec x y) (only parsing).

  Definition isgap`(w : wavltree k g lg rg c)(g' : bool) : {k >= #0 /\ #g' = g} + {k= - #1 \/ #g' <> g}.
  Proof.
    ?? w.
    1: ?? (g' ?= (gap w)).
    !!.
  Qed.

End IsGap.
 
Section IsMissing.

  Tactic Notation "!!" := [>constructor; boom..].

  Definition isMissing`(w : wavltree k g lg rg c) : {c = [] /\ k = - #1} + {c <> [] /\ k >= #0}.
  Proof. ?? w. !!. Qed.

End IsMissing.

(*Constructing a general way to solve wavltree-conclusion goals that will
culminate with solve_wavl, which will attempt to solve each wavltree goal in
one of three ways: using a Missing tree, by assumption, or by Node
construction - in that order.*)

Ltac wavl_missing :=
  eapply Missing;
  [reflexivity (* c = [] *)
  |boom.. (*k/lg/rg*)
  ].

Ltac wavl_assumption :=
  multimatch goal with W:wavltree _ _ _ _ ?C |- wavltree _ _ _ _ ?C' =>
    replace C' with C by (rewrite ?Eapp_assoc; reflexivity);
    (force exact W + force refine (setgap W _))
  end;[boom..].

(*Note that wavl_assumption must be more than just "eassumption" because
eassumption requires that the assumption's type parameters match the conclusion
syntactically (roughly), not semantically (the actual requirement is that they
be unifiable - which is mostly syntatic).  For example, C and C' may not
directly unify until after canonizalizing their associativity. Also, eassumption
does not produce multiple solutions for backtracking.  We need semantic matching
with backtracking because even ring_simplify cannot guarantee canonical forms of
ring terms that may involve evars - or, a better way to say this is that there
is no canonical-form-based syntactic matching procedure that can involve evars
and permit all possible instantiations of those evars that would produce
semantic matches.  For example, consider matching terms 2 and ?x + ?y in Z.
They aren't directly unifiable, but there are many semantic matches.  The best
procedure is to solve the induced equality to something like ?x = 2 - ?y, then
unify the lhs and rhs.  Because Z is a ring with + invertable to -, this one
solution is general.  However, because booleans may be present in the wavltree
rank terms (via coercion), an induced equality involving only boolean evars may
not always have a single general solution, hence the need for backtracking over
successes.  These semantic solutions are generated by the boom tactic.

Instead of eassumption, we use the "force exact" and "force refine" tacticals
from utils.v within a multimatch.  The multimatch, "+" tactical, and the usage
of boom, provide backtracking over successes.  The force tacticals create
equality subgoals for each non-trivially-matching type parameter, which can
then be solved (with possibly multiple successes) via boom.  We can restrict
the attempted assumptions (to speed things up) to just those that have the
same contents modulo associativity - which is handled by the replace tactic
prior to force exact.  The reason for the force refine of setgap is that we
also want to try assumptions that may need their gaps modified in some way to
produce solutions.*)

Ltac solve_wavl :=
  dintros;
  (wavl_missing + wavl_assumption + wavl_construction)
with wavl_construction :=
  reassoc;
  eapply Node;
  [reflexivity (* #g = pg *)
  |reflexivity (* c = lc++[d]++rc *)
  |solve_wavl (*lw*)
  |solve_wavl (*rw*)
  |boom (*leaf_rule*)
  |ss (* Esorted c *)
  ].

(*Note that reflexivity is sufficient to solve the "#g = pg" and "c =
lc++[d]++rc" subgoals above.  In the first case, this is because g is introduced
by Node, and so will always be an evar in this equation - and pg will itself
either be an evar or a "#"'ed term due to our usage.  In the second case, this
is because of the reassoc tactic, and the fact that lc, d and rc will always be
evars due to being introduced by Node. *)

Section Insert_Rotations.

  (*These two insert rotation functions were created for goals encountered
  within the insert function (below) that involve constructing a wavltree when
  the required (based on contents) wavltree assumptions differ in rank by 2.
  That they are "rotations" only becomes evident when viewing the extracted
  source.  However, in terms of the proofs, the decision to separate these
  functions is based on the need to case-analyze more than just one level of
  wavltree.  All of the non-rotation functions directly case analyze (other
  than by auxiliary function such as isgap, isMissing, etc.) just one wavltree
  argument, as their first proof step - which implies that they never have
  multiple generations of wavltrees available as assumptions, and so cannot
  perform rotations.  This demonstrates how certain meta-logical structuring
  of the proofs can induce some nice modularization properties (rotations are
  separate functions) in the extracted code.*)

  Tactic Notation "!!" := [>solve_wavl..].

  Definition irot1`(lw : wavltree k #false llg lrg lc)(x : A)`(rw : wavltree (k - #2) #true rlg rrg rc)
    : llg = Enegb lrg -> Esorted(lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc).
  Proof.
    ?? lw.
    - ?? (right_child lw).
      + ?? (gap (right_child lw)). !!.
      + !!.
    - !.
  Qed.

  Definition irot2`(lw : wavltree (k - #2) #true llg lrg lc)(x : A)`(rw : wavltree k #false rlg rrg rc)
    : Enegb rlg = rrg -> Esorted(lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc).
  Proof.
    ?? rw.
    - ?? (left_child rw).
      + ?? (gap (left_child rw)). !!.
      + !!.
    - !.
  Qed.

End Insert_Rotations.

(*We will construct other rotation functions later for delete (and its helper
functions), but all will have a similar parameterization, which allows us to
create a single tactic to use them.  Note that we only try assumptions to fill
in the wavltree parameters for rotations.  Care must be taken so that the
conclusions of the rotation functions are unifiable via eapply with all
potential goal conclusions, else we would need to use force refine instead to
generate extra equality subgoals.*)

Ltac use_rotations r1 r2 :=
  dintros;
  reassoc;
  (eapply r1 + eapply r2);
  [wavl_assumption (*lw*)
  |wavl_assumption (*rw*)
  |boom (*_lg<>_rg*)
  |ss (*Esorted*)
  ].

(*There will be times when wavltrees can have their gaps "unerased" even in a
non-Prop goal, because it is provable that the wavltree is not Missing and
hence has a real gap field.  The following unerase_gaps tactic does this.  It
can be used to allow case analysis of gaps directly (instead of using the
isgap function), and it can also be used prior to a wavl_assumption to allow
its setgap call to be solved based on those unerased gaps.  Unfortunately, it
cannot be called only when the need is established, because of Coq's rules
about evar scopes (meaning that a gap must be unerased prior to the
introduction of any evar it is meant to fill).*)

Ltac unerase_gaps :=
  subst;
  let f H :=
      try
        lazymatch type of H with
          wavltree _ ?G _ _ _ =>
          is_var G; (*H is a suitable target for gap unerasure*)
          case (getgap H); (*do the unerasure by calling getgap...*)
          let X := fresh in
          let G' := fresh in
          intros G' X;
          (*...and then attempt to prove that H isn't missing, so that getgap
          can produce the gap*)
          first [specialize (X ltac:(assumption||fnenil))
                |specialize (X (wavl_node_nonempty H ltac:(bang)))];
          (*If the above proof works, we can replace the old erasable gap var
          with the new unerased one, keeping the old one's name:*)
          rewrite <-X in *;
          clear X G;
          rename G' into G
        end in
    allhyps_td f.

Section Insert.

  (*For insert and some of the remaining functions, we will compose the result
  type from multiple parts.  The "innermost" part (instertedHow here) will
  become an enumeration on extraction - with no "informative" fields.  It is
  separated out just for clarity.  Other parts (Delout for the delete
  functions below) allow sharing of sub-result types.*)

  Inductive insertedHow(ik ok : EZ)(ig og olg org : EB) : Set :=
  | ISameK(_: ok = ik)(_: og = ig)
  | IWasMissing(_: ik = - #1)(_: ok = #0)(_: og = #false)
  | IHigherK(_: ik >= #0)(_: ok = ik + #1)(_: olg = Enegb org)(_: og = #false).

  (*Note that insertedHow only needs 2 ctors - ISameK and IHigherK.  However,
  by adding IWasMissing, we can avoid some redundant casing.  The same idea
  doesn't work as well with the delete functions. *)

  Inductive insertResult(x: A)(k : EZ)(g lg rg : EB)(c : EL) : Set :=
  | Inserted`(_: c = lc++rc)
            `(ow: wavltree ok og olg org (lc++[x]++rc))
            `(_: insertedHow k ok g og olg org)
  | FoundByInsert`(_: c = lc++[x]++rc).

  (*Augment the generic solve_wavl with the rotation functions:*)
  Ltac solve_wavl2 := use_rotations irot1 irot2 + solve_wavl.

  (* This lemma covers the case where c is [], which can't be solved by
  reflexivity vs. ?lc++?rc (two evars appended).*)
  Lemma nilnilnil : [] = [] ++ [] :> EL.
  Proof.
    rewrite Eapp_nil_l.
    reflexivity.
  Qed.

  Ltac solve_insert :=
    dintros;
    reassoc;
    ((eapply FoundByInsert; reflexivity) +
     (eapply Inserted;
      [reflexivity || eapply nilnilnil (* c = lc++rc *)
      |solve_wavl2 (*ow*)
      |econstructor;[boom..] (*insertedHow*)
    ])).

  (*Why do we solve for the output wavltree (ow) before solving for
  insertedHow?  Only because it is about 8X faster this way, and doesn't alter
  the extracted output.  However, it certainly would make sense to solve for
  insertedHow first, and thus be able to force the proof search to favor
  ISameK over IHigherK by trying all possible ISameK successes first.*)

  Tactic Notation "!!" := [>solve_insert..].

  Fixpoint insert(x : A)`(w : wavltree k g lg rg c) : insertResult x k g lg rg c.
  Proof.
    ?? w.
    - ?? (x =<> (datum w)).
      + !!.
      + ?? (insert x) on (left_child w).
        * ?? (pick insertedHow).
          -- !!.
          -- ?? (isMissing (right_child w)). !!.
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ !!.
             ++ ?? (isgap (right_child w) false). !!.
        * !!.
      + ?? (insert x) on (right_child w).
        * ?? (pick insertedHow).
          -- !!.
          -- ?? (isMissing (left_child w)). !!.
          -- unerase_gaps. ?? (gap (right_child w)).
             ++ !!.
             ++ ?? (isgap (left_child w) false). !!.
        * !!.
    - !!.
  Qed.

  (*Note: in both cases above when we use unerase_gaps, followed by casing a
  gap, we could instead have cased on (isgap child true) without using
  unerase_gaps, as is done elsewhere.  Maybe there's a very small performance
  advantage, as the getgap function (which is what extracts when casing an
  unerased gap directly) contains fewer conditionals than the isgap
  function.*)

End Insert.

(**********************************************************************)

Section TryLowering.

  (*tryLowering is a helper function for deletions - it tries to reduce the
  rank of a wavltree by 1 in the most trivial way - by removing the gaps (if
  they are both present) from both immediate children of its root.  Even if
  the lowering fails, we learn something about those gaps that is needed for
  calling the delete rotations (below).*)

  Inductive tryLoweringResult(k : EZ)(g lg rg : EB)(c : EL) : Set :=
  | TLlowered(_: lg = #true)(_: rg = #true)(ow: wavltree (k - #1) g #false #false c)
  | TLtooLow(_: lg = #false \/ rg = #false).

  Ltac solve_tl :=
    dintros;
    ((eapply TLlowered;
      [reflexivity (*lg*)
      |reflexivity (*rg*)
      |solve_wavl (*ow*)
     ])
     || (eapply TLtooLow; boom)).

  Tactic Notation "!!" := [>solve_tl..].

  Definition tryLowering`(w : wavltree k g lg rg c) : tryLoweringResult k g lg rg c.
  Proof.
    ?? w.
    - ?? (isgap (left_child w) true).
      + ?? (isgap (right_child w) true). !!.
      + !!.
    - !!.
  Qed.

End TryLowering.

(*The remaining deletion functions will share the following result parts, and
solve_delpair solver tactic:*)

Inductive deletedHow(ik ok : EZ)(ig og : EB) : Set :=
| DSameK(_: ok = ik)(_: og = ig)
| DLowerK(_:  ok = ik - #1)(_: og = #true).

Inductive delpair(k : EZ)(g : EB)(c : EL) : Set :=
| Delout`(dh : deletedHow k ok g og)`(ow : wavltree ok og olg org c).

Ltac solve_delpair :=
  dintros;
  eapply Delout;
  [constructor; [boom..] (*dh*)
  |solve_wavl (*ow*)
  ].

Section Delete_Rotations.
  
  (*These two delete rotation functions were created for goals within the
  delete function (later) that involve constructing a wavltree when the
  wavltree assumptions differ in rank by 2.  That they are "rotations" only
  becomes evident when viewing the extracted source.*)

  (*Note: these two functions take the longest to prove.  About 15 minutes a
  piece, depending obviously on hardware.*)

  Tactic Notation "!!" := [>solve_delpair..].

  Definition drot1`(lw : wavltree (k - #3) #true llg lrg lc)(x : A)`(rw : wavltree (k - #1) #false rlg rrg rc)
    : rlg = #false \/ rrg = #false -> Esorted(lc++[x]++rc) -> forall g, delpair k #g (lc++[x]++rc).
  Proof.
    ?? rw.
    - ?? (left_child rw).
      + ?? (isgap (right_child rw) false); !!.
      + !!.
    - !.
  Qed.

  Definition drot2`(lw : wavltree (k - #1) #false llg lrg lc)(x : A)`(rw : wavltree (k - #3) #true rlg rrg rc)
    : llg = #false \/ lrg = #false -> Esorted(lc++[x]++rc) -> forall g, delpair k #g (lc++[x]++rc).
  Proof.
    ?? lw.
    - ?? (right_child lw).
      + ?? (isgap (left_child lw) false). !!.
      + !!.
    - !.
  Qed.

End Delete_Rotations.

(*Again, using the above rotations to augment a solver, this time solve_delpair:*)
Ltac solve_delpair2 := use_rotations drot1 drot2 + solve_delpair.

Section Delete_Minimum.

  (*Before defining delete, we first need at least one of the following two
  functions: delmin and delmax.  These are used by delete to find a replacement
  for the deleted datum.  Although we need only one, we'll define and use
  both. *)

  Inductive delminResult(k : EZ)(g : EB)(c : EL) : Set :=
    MinDeleted(min : A)`(_: c = [min]++rc)(dp : delpair k g rc).

  Ltac solve_delmin :=
    dintros;
    reassoc;
    try rewrite Eapp_nil_l; (*removes leading []++...*)
    eapply MinDeleted;
    [reflexivity|solve_delpair2].

  Tactic Notation "!!" := [>solve_delmin..].

  Fixpoint delmin`(w : wavltree k g lg rg c) : k >= #0 -> delminResult k g c.
  Proof.
    ?? w.
    - ?? (isMissing (left_child w)).
      + !!.
      + ?? delmin on (left_child w).
        * !.
        * ?? (pick delpair). ?? (pick deletedHow).
          -- !!.
          -- ?? (isgap (right_child w) false).
             ++ ?? (isgap (left_child w) true).
                ** ?? (tryLowering (right_child w)). !!.
                ** !!.
             ++ unerase_gaps. !!.
    - !.
  Qed.

End Delete_Minimum.

Section Delete_Maximum.

  Inductive delmaxResult(k : EZ)(g : EB)(c : EL) : Set :=
   MaxDeleted(max : A)`(_: c = lc++[max])(dp : delpair k g lc).

  Ltac solve_delmax :=
    dintros;
    reassoc;
    try rewrite Eapp_nil_r; (*removes trailing ...++[]*)
    eapply MaxDeleted;
    [reflexivity|solve_delpair2].

  Tactic Notation "!!" := [>solve_delmax..].

  Fixpoint delmax`(w : wavltree k g lg rg c) : k >= #0 -> delmaxResult k g c.
  Proof.
    ?? w.
    - ?? (isMissing (right_child w)).
      + !!.
      + ?? delmax on (right_child w).
        * !.
        * ?? (pick delpair). ?? (pick deletedHow).
          -- !!.
          -- ?? (isgap (left_child w) false).
             ++ ?? (isgap (right_child w) true).
                ** ?? (tryLowering (left_child w)). !!.
                ** !!.
             ++ unerase_gaps. !!.
    - !.
  Qed.

End Delete_Maximum.

Section Delete.

  (*Finally - delete - which is often omitted from formal treatments of
  balanced binary trees due to its proof complexity.  However, the
  infrastructure created here can handle it without difficulty.*)

  Inductive deleteResult(x : A)(k : EZ)(g : EB)(c : EL) : Set :=
  | Deleted`(_: c = lc++[x]++rc)(dp : delpair k g (lc++rc))
  | DNotFound(_: ENotIn x c).

  Ltac solve_delete :=
    dintros;
    reassoc;
    ((eapply Deleted;
      [reflexivity (* c = lc++[x]++rc *)
      |(rewrite Eapp_nil_r + rewrite Eapp_nil_l + idtac); solve_delpair2
      ])
     + (eapply DNotFound; ss)).

  Tactic Notation "!!" := [>solve_delete..].

  Fixpoint delete(x : A)`(w : wavltree k g lg rg c) : deleteResult x k g c.
  Proof.
    ?? w.
    - ?? (x =<> (datum w)).
      + ?? (isMissing (left_child w)).
        * !!.
        * ?? (isMissing (right_child w)).
          -- !!.
          -- (*decide whether to replace the root datum using delmin on the
             right child or delmax on the left by examining either child's
             gap, preferring to delete from a child with no gap (higher rank),
             if there is one.*)
             unerase_gaps. ?? (gap (left_child w)).
             ++ ?? (delmin (right_child w)).
                ** !.
                ** ?? (pick delpair). ?? (pick deletedHow). !!.
             ++ ?? (delmax (left_child w)).
                ** !.
                ** ?? (pick delpair). ?? (pick deletedHow). !!.
      + ?? (delete x) on (left_child w).
        * ?? (pick delpair). ?? (pick deletedHow).
          -- !!.
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ unerase_gaps. ?? (gap (right_child w)).
                ** !!.
                ** ?? (tryLowering (right_child w)). !!.
             ++ ?? (isMissing (right_child w)). !!.
        * !!.
      + ?? (delete x) on (right_child w).
        * ?? (pick delpair). ?? (pick deletedHow).
          -- !!.
          -- unerase_gaps. ?? (gap (right_child w)).
             ++ unerase_gaps. ?? (gap (left_child w)).
                ** !!.
                ** ?? (tryLowering (left_child w)). !!.
             ++ ?? (isMissing (left_child w)). !!.
        * !!.
    - !!.
  Qed.

End Delete.
Show Ltac Profile.
Set Printing Width 120.

Require Import ExtrOcamlBasic.

Extract Inductive delpair => "( * )" [ "" ].
Extract Inductive delminResult => "( * )" [ "" ].
Extract Inductive delmaxResult => "( * )" [ "" ].

Extraction Inline negb.

Extract Inlined Constant Bool.bool_dec => "(=)".

Extraction "wavl.ml" find insert delete.


(* Local Variables: *)
(* company-coq-local-symbols: (("++" . ?⧺) ("Esorted" . ?⊿) ("#" . ?◻) ("wavltree" . ?🎄) ("[]" . ?∅) ("^" . ?⋄) ("^#" . ?⟎) ("Enegb" . ?¬) ("true" . ?Ṫ) ("false" . ?Ḟ) ("EL" . ?Ḷ) ("EB" . ?Ḅ) ("EZ" . ?Ẓ)) *)
(* End: *)
