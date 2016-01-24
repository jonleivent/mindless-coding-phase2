(***********************************************************************

Copyright (c) 2015 Jonathan Leivent

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

(* This is a type-index-less version of wavl.v.  Removing type indexes makes
Coq's destruct tactic work for all case analyses - so there is no need for the
mindless user to have to decide between inversion, destruct, case, etc. (this
is not a big deal - it just demonstrates that even peculiar Coq-isms
pertaining to using highly-dependent types can be dealt with by taking some
simple precautions - as well as demonstrates that the number of tactics one
needs to have in their toolbox is quite small).  Also in this version, all
user-built (solve_...) tactics are removed to show the contrast with wavl.v,
where they provide considerable benefits.  The match tactics used to select
hypotheses in proofs have also been removed so that a user stepping through
the proofs may more clearly see what is going on.  What is not shown is that,
without the backtracking user-built tactics, the user will have to undo and
redo many parts of these proofs before they are accepted.  Because the removed
backtracking tactics are slow, the result of not using them is that this file
goes through Coq about 4X faster than wavl.v. *)

Require Import elist.
Require Import ezbool.
Require Import ExtrOcamlBasic.
Require Import utils.
Require Import posall.
Require Import hypiter.

Generalizable All Variables.

Context {A : Set}.

Context {ordA : Ordered A}. 

Notation EL := ##(list A).

Inductive wavltree(k : EZ)(g lg rg : EB)(f : EL) : Set :=
| Missing
    (eqf : f = [])
    (eqk : k = #- #1)
    (eqlg : lg = #false)
    (eqrg : rg = #false)
| Node
    (ug : bool)
    (equg : g = #ug)
    `(eqlk : lk = k #- #1 #- Eb2Z lg)
    `(lc : wavltree lk lg llg lrg lf)
    (d : A)
    `(eqrk : rk = k #- #1 #- Eb2Z rg)
    `(rc : wavltree rk rg rlg rrg rf)
    (s : Esorted (lf ++ ^d ++ rf))
    (leaf : k = #1 -> lk = #0 \/ rk = #0)
    (eqf : f = lf ++ ^d ++ rf).

Lemma wavlkgtm1 : forall `(t : wavltree ek g lg rg f), exists k, #k = ek /\ k >= -1.
Proof.
  dintros.
  induction t.
  - unerase.
    omega.
  - unerase.
    posall b2Zbounds.
    omega.
Qed.

Lemma wavlkge0 : forall `(t : wavltree ek g lg rg f), f <> [] -> exists k, #k = ek /\ k >= 0.
Proof.
  dintros.
  destruct t; dintros.
  - tauto.
  - posall @wavlkgtm1.
    unerase.
    posall b2Zbounds.
    omega.
Qed.

Lemma wavlfnenil :
  forall `(t : wavltree k g lg rg f), k <> #- #1 -> f <> [].
Proof.
  dintros.
  destruct t; dintros.
  - tauto.
  - fnenil.
Qed.

Lemma clearleaf1 : forall `(t : wavltree (#- #1) g lg rg f), f= [ ] /\ lg = #false /\ rg = #false.
Proof.
  dintros.
  destruct t; dintros.
  - tauto.
  - posall @wavlkgtm1.
    unerase.
    posall b2Zbounds.
    exfalso.
    omega.
Qed.

Lemma clearleaf2 : forall `(t : wavltree k g lg rg []), k = #- #1 /\ lg = #false /\ rg = #false.
Proof.
  dintros.
  destruct t; dintros.
  - tauto.
  - fnenil.
Qed.

Ltac bang_setup_tactic ::=
  let f H :=
      lazymatch type of H with
      | wavltree _ _ _ _ _ =>
        first [apply clearleaf1 in H
              |apply clearleaf2 in H
              |pose proof (wavlkge0 H ltac:(assumption||fnenil))
              |pose proof (wavlkgtm1 H)
              ]
      | _ => idtac
      end
  in
  hyps => loop f.

Tactic Notation "boom" := boom_internal false.

Definition isMissing`(t : wavltree ek g lg rg f)
  : {f = [] /\ lg = #false /\ rg = #false /\ exists k, #k = ek /\ k = -1} + {f <> [] /\ exists k, #k = ek /\ k >= 0}.
Proof.
  destruct t; dintros.
  - left.
    boom.
  - right.
    boom.
Qed.

Lemma wavls : forall `(t : wavltree k g lg rg f), Esorted f.
Proof.
  dintros.
  onhead wavltree destr; dintros.
  - unerase.
    solve_sorted.
  -  assumption.
Qed.

Ltac ss_setup_tactic := 
  let f H := try apply wavls in H in
  hyps => loop f.

Ltac ss := ss_setup_tactic; unerase; solve_sorted.

Inductive findResult(x : A)(f : EL) : Set :=
| Found`(eqf : f = fl ++ ^x ++ fr)
| NotFound(ni : ENotIn x f).

Definition find(x : A)`(t : wavltree k g lg rg f) : findResult x f.
Proof.
  onhead wavltree induct; dintros.
  - eapply NotFound.
    ss.
  - destruct (compare_spec x d); dintros.
    + eapply Found.
      reflexivity.
    + destruct IHt1; dintros.
      * (*rootify alters the associativity of the contents list until the
        specified datum is at the "root" position for a node:*)
        rootify x.
        eapply Found.
        reflexivity.
      * apply NotFound.
        ss.
    + destruct IHt2; dintros.
      * rootify x.
        eapply Found.
        reflexivity.
      * apply NotFound.
        ss.
Qed.

Definition setgap`(t : wavltree k ig lg rg f)(g : bool) : wavltree k #g lg rg f.
Proof.
  destruct t; dintros.
  - apply Missing.
    all:reflexivity.
  - eapply Node.
    (*solve the contents subgoal first to make it easier to identify parts of
    other subgoals by their contents:*)
    all:[>..|reflexivity].
    boom.
    boom.
    (*force exact is like exact, but turns non-simply-unifiable args (some of
    which would cause exact to fail) into equation subgoals.  It is especially
    useful when type parameters have complex term arguments that might be
    equal semantically but not by pattern (the ranks of wavltrees tend to do
    this often).*)
    force exact t1.
    boom.
    boom.
    force exact t2.
    boom.
    ss.
    boom.
Qed.

Definition getgap`(t : wavltree k eg lg rg f) : { g | f <> [] -> #g = eg}.
Proof.
  destruct t; dintros.
  - eexists.
    boom.
  - eexists.
    boom.
Grab Existential Variables.
  exact false.
Qed.

Definition gofis`(t : wavltree k eg lg rg f)(g : bool) : {k<> #- #1 /\ #g = eg} + {k=#- #1 \/ #g <> eg}.
Proof.
  destruct t; dintros.
  { right; tauto. }
  compare g ug; dintros.
  - left.
    split.
    + boom.
    + reflexivity.
  - right.
    right.
    unerase.
    assumption.
Qed.

(*Some abbreviation tactics.*)
Ltac node := eapply Node; [..|reflexivity].
Ltac missing := eapply Missing.
Ltac gap := eapply setgap.

Definition rot1
           `(lt : wavltree k #false llg lrg lf)
           (x : A)
           `(rt : wavltree (k #- #2) #true rlg rrg rf)
           (gne : llg <> lrg)
           (s : Esorted (lf ++ ^x ++ rf))
  : forall g, wavltree k #g #false #false (lf ++ ^x ++ rf).
Proof.
  intro g.
  destruct lt; dintros.
  { tauto. }
  destruct lt2; dintros.
  - (*minlines just makes the context easier to read by re-arranging
    hypotheses so that they occupy the fewest number of lines*)
    minlines.
    rootify d.
    node.
    boom.
    boom.
    force exact lt1.
    boom.
    boom.
    boom.
    node.
    boom.
    boom.
    missing.
    reflexivity.
    boom_internal true.
    boom.
    boom.
    boom.
    gap.
    force exact rt.
    boom.
    ss.
    boom.
    ss.
    boom.
  - minlines.
    destruct ug0.
    + rootify d.
      node.
      boom.
      boom.
      force exact lt1.
      boom.
      boom.
      boom.
      rootify x.
      node.
      boom.
      boom.
      node.
      boom.
      boom.
      force exact lt2_1.
      boom.
      boom.
      force exact lt2_2.
      boom.
      ss.
      boom.
      boom.
      gap.
      force exact rt.
      boom.
      ss.
      boom.
      ss.
      boom.
    + rootify d0.
      node.
      boom.
      boom.
      node.
      boom.
      boom.
      gap.
      force exact lt1.
      boom_internal true.
      boom.
      force exact lt2_1.
      boom.
      ss.
      boom.
      boom.
      node.
      boom.
      boom.
      force exact lt2_2.
      boom.
      boom.
      gap.
      force exact rt.
      boom.
      ss.
      boom.
      ss.
      boom.
Qed.

Extraction rot1.

Definition rot2
           `(lt : wavltree (k #- #2) #true llg lrg lf)
           (x : A)
           `(rt : wavltree k #false rlg rrg rf)
           (gne : rlg <> rrg)
           (s : Esorted (lf ++ ^x ++ rf))
  : forall g, wavltree k #g #false #false (lf ++ ^x ++ rf).
Proof.
  intro g.
  destruct rt; dintros.
  { tauto. }
  destruct rt1; dintros.
  - minlines.
    rootify d.
    node.
    boom.
    boom.
    node.
    boom.
    boom.
    gap.
    force exact lt.
    boom.
    boom.
    missing.
    boom.
    boom_internal true.
    boom.
    boom.
    ss.
    boom.
    boom.
    force exact rt2.
    boom.
    boom.
    ss.
    boom.
  - minlines.
    destruct ug0.
    + rootify d.
      node.
      boom.
      boom.
      node.
      boom.
      boom.
      gap.
      force exact lt.
      boom.
      boom.
      node.
      boom.
      boom.
      force exact rt1_1.
      boom.
      boom.
      force exact rt1_2.
      boom.
      ss.
      boom.
      ss.
      boom.
      boom.
      force exact rt2.
      boom.
      boom.
      ss.
      boom.
    + rootify d0.
      node.
      boom.
      boom.
      node.
      boom.
      boom.
      gap.
      force exact lt.
      boom.
      boom.
      force exact rt1_1.
      boom.
      ss.
      boom.
      boom.
      node.
      boom.
      boom.
      force exact rt1_2.
      boom.
      boom.
      gap.
      force exact rt2.
      boom_internal true.
      ss.
      boom.
      ss.
      boom.
Qed.

Inductive insertedHow(ki ko : EZ)(gi go lgo rgo : EB)(f : EL) : Set :=
| ISameK(_: ko = ki)(_: f <> [])(_: go = gi)
| IWasMissing(_: ki= #- #1)(_: ko = #0)(_: f = [])(_: go = #false)
| IHigherK(_: ko=ki #+ #1)(_: lgo <> rgo)(_: f <> [])(_: go = #false).

Inductive insertResult(x: A)(k : EZ)(g lg rg : EB)(f : EL) : Set :=
| FoundByInsert`(eqf : f=fl ++ ^x ++ fr)
| Inserted`(eqf : f = fl ++ fr)
          `(t : wavltree ko go lgo rgo (fl ++ ^x ++ fr))
          (i : insertedHow k ko g go lgo rgo f).

Ltac unerase_gaps :=
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
  induction t; dintros.
  - eapply Inserted.
    change ([]:EL) with ([] ++ []:EL).
    reflexivity.
    node.
    boom.
    boom.
    missing.
    reflexivity.
    boom.
    boom.
    boom.
    boom.
    missing.
    reflexivity.
    boom.
    boom.
    boom.
    ss.
    boom_internal true.
    eapply IWasMissing.
    boom.
    boom.
    reflexivity.
    boom.
  - destruct (compare_spec x d); dintros.
    + eapply FoundByInsert.
      reflexivity.
    + destruct IHt1; dintros.
      * rootify x.
        eapply FoundByInsert.
        reflexivity.
      * onhead insertedHow destr; dintros.
        -- (*rootify would not work here, so the tactic assoc N reassociates
           the contents list so that only the leftmost N sublists are
           associated together:*)
           assoc 0.
           eapply Inserted.
           reflexivity.
           rootify d.
           node.
           boom.
           boom.
           force exact t.
           boom.
           force exact t2.
           boom.
           ss.
           boom.
           eapply ISameK.
           boom.
           fnenil.
           boom.
        -- destruct (isMissing t2); dintros.
           ++ assoc 0.
              eapply Inserted.
              reflexivity.
              rootify d.
              node.
              boom.
              boom.
              force exact t.
              boom.
              missing.
              reflexivity.
              boom.
              boom.
              boom.
              ss.
              boom.
              eapply IHigherK.
              boom.
              boom.
              fnenil.
              boom.
           ++ assoc 0.
              eapply Inserted.
              reflexivity.
              rootify d.
              node.
              boom.
              boom.
              force exact t.
              boom.
              force exact t2.
              boom.
              ss.
              boom.
              eapply ISameK.
              boom.
              fnenil.
              boom.
        -- unerase_gaps.
           destruct lg; dintros.
           ++ minlines.
              assoc 0.
              eapply Inserted.
              reflexivity.
              rootify d.
              node.
              boom.
              boom.
              force exact t.
              boom.
              force exact t2.
              boom.
              ss.
              boom.
              eapply ISameK.
              boom.
              fnenil.
              boom.
           ++ destruct (gofis t2 false); dintros.
              ** assoc 0.
                 eapply Inserted.
                 reflexivity.
                 rootify d.
                 node.
                 boom.
                 boom.
                 force exact t.
                 boom.
                 gap.
                 force exact t2.
                 boom.
                 ss.
                 boom.
                 eapply IHigherK.
                 boom.
                 boom.
                 fnenil.
                 boom.
              ** assoc 0.
                 eapply Inserted.
                 reflexivity.
                 rootify d.
                 eapply rot1.
                 force exact t.
                 force exact t2.
                 boom.
                 boom.
                 assumption.
                 ss.
                 eapply ISameK.
                 boom.
                 fnenil.
                 boom.
    + destruct IHt2;dintros.
      * rootify x.
        eapply FoundByInsert.
        reflexivity.
      * onhead insertedHow destr; dintros.
        -- assoc 2.
           eapply Inserted.
           reflexivity.
           rootify d.
           node.
           boom.
           boom.
           force exact t1.
           boom.
           force exact t.
           boom.
           ss.
           boom.
           eapply ISameK.
           boom.
           fnenil.
           boom.
        -- destruct (isMissing t1); dintros.
           ++ assoc 2.
              eapply Inserted.
              reflexivity.
              rootify d.
              node.
              boom.
              boom.
              missing.
              reflexivity.
              boom.
              boom.
              boom.
              boom.
              force exact t.
              boom.
              ss.
              boom.
              eapply IHigherK.
              boom.
              boom.
              fnenil.
              boom.
           ++ assoc 2.
              eapply Inserted.
              reflexivity.
              rootify d.
              node.
              boom.
              boom.
              force exact t1.
              boom.
              force exact t.
              boom.
              ss.
              boom.
              eapply ISameK.
              boom.
              fnenil.
              boom.
        -- unerase_gaps.
           destruct rg; dintros.
           ++ minlines.
              assoc 2.
              eapply Inserted.
              reflexivity.
              rootify d.
              node.
              boom.
              boom.
              force exact t1.
              boom.
              force exact t.
              boom.
              ss.
              boom.
              eapply ISameK.
              boom.
              fnenil.
              boom.
           ++ destruct (gofis t1 false); dintros.
              ** minlines.
                 assoc 2.
                 eapply Inserted.
                 reflexivity.
                 rootify d.
                 node.
                 boom.
                 boom.
                 gap.
                 force exact t1.
                 boom.
                 force exact t.
                 boom.
                 ss.
                 boom.
                 eapply IHigherK.
                 boom.
                 boom.
                 fnenil.
                 boom.
              ** minlines.
                 assoc 2.
                 eapply Inserted.
                 reflexivity.
                 rootify d.
                 eapply rot2.
                 force exact t1.
                 boom.
                 boom.
                 force exact t.
                 boom.
                 assumption.
                 ss.
                 eapply ISameK.
                 boom.
                 fnenil.
                 boom.
Qed.

(**********************************************************************)

Inductive tryLoweringResult`(t : wavltree k g lg rg f) : Set :=
| TLtooLow(p : lg = #false \/ rg = #false)
| TLlowered(p: lg = #true /\ rg = #true)(t': wavltree (k #- #1) g #false #false f).

Definition tryLowering`(t : wavltree k g lg rg f) : tryLoweringResult t.
Proof.
  destruct t.
  - eapply TLtooLow.
    boom.
  - destruct (gofis t2 true).
    + destruct (gofis t1 true).
      * eapply TLlowered.
        boom.
        subst.
        node.
        boom.
        boom.
        gap.
        force exact t1.
        boom.
        boom.
        gap.
        force exact t2.
        boom.
        ss.
        boom.
      * eapply TLtooLow.
        boom.
    + eapply TLtooLow.
      boom.
Qed.

Inductive deletedHow(ki ko : EZ)(gi go : EB) : Set :=
| DSameK(keq : ko = ki)(eg : go = gi)
| DLowerK(keq :  ki = ko #+ #1)(eg: go = #true).

Inductive delpair(k : EZ)(g : EB)(f : EL) : Set :=
| Delout`(t : wavltree ko go lgo rgo f)(d : deletedHow k ko g go).

Definition drot1
           `(t : wavltree (k #- #3) #true lgo rgo f)
           (d : A)
           `(t2 : wavltree (k #- #1) #false rlg rrg rf)
           (s : Esorted (f ++ ^ d ++ rf))
           (tltl : rlg = #false \/ rrg = #false)
  : forall ug, delpair k #ug (f ++ ^d ++ rf).
Proof.
  intro ug.
  destruct t2; dintros.
  { boom. }
  destruct (t2_1); dintros.
  - minlines.
    rootify d0.
    eapply Delout.
    node.
    boom.
    boom.
    node.
    boom.
    boom.
    gap.
    force exact t.
    boom.
    missing.
    reflexivity.
    boom_internal true.
    boom.
    boom.
    ss.
    boom_internal true.
    boom.
    gap.
    force exact t2_2.
    boom_internal true.
    ss.
    boom.
    eapply DSameK.
    boom.
    boom.
  - minlines.
    destruct (gofis t2_2 false); dintros.
    + rootify d0.
      eapply Delout.
      node.
      boom.
      boom.
      rootify d.
      node.
      boom.
      boom.
      force exact t.
      boom.
      force exact t2_1.
      boom.
      ss.
      boom.
      boom.
      gap.
      force exact t2_2.
      rsimp.
      boom_internal true. (**)
      ss.
      boom.
      eapply DSameK.
      boom.
      boom.
    + rootify d1.
      eapply Delout.
      node.
      boom.
      boom.
      node.
      boom.
      boom.
      gap.
      force exact t.
      boom.
      force exact w1.
      boom_internal true.
      ss.
      boom.
      boom.
      node.
      boom.
      boom.
      force exact w2.
      boom_internal true.
      boom.
      gap.
      force exact t2_2.
      boom_internal true.
      ss.
      boom.
      ss.
      boom_internal true.
      eapply DSameK.
      boom.
      boom.
Qed.

Definition drot2
           `(t2 : wavltree (k #- #1) #false llg lrg lf)
           (d : A)
           `(t : wavltree (k #- #3) #true lgo rgo f)
           (s : Esorted (lf ++ ^ d ++ f))
           (tltl : llg = #false \/ lrg = #false)
  : forall ug, delpair k #ug (lf ++ ^d ++ f).
Proof.
  intro ug.
  destruct t2; dintros.
  { boom. }
  destruct (t2_2); dintros.
  - minlines.
    rootify d0.
    eapply Delout.
    node.
    boom.
    boom.
    gap.
    force exact t2_1.
    boom.
    node.
    boom.
    boom.
    missing.
    reflexivity.
    (*This is the first case where boom would select as its first solution one
    that is not suitable for the rest of the proof.  One way to suspect such
    of a goal: if it contains multiple evars for gaps (bool or EB), but none
    for ranks (EZ).  We can delay these goals until later using all:cycle 1,
    hoping that other goals fill in some or all of those evars, or that we end
    up with a bunch of such goals we can just try to solve together under a
    single all:boom call (actually, all:[>boom..] is faster).*)
    all:cycle 1.
    boom.
    boom.
    boom.
    gap.
    force exact t.
    all:cycle 1.
    ss.
    all:cycle 1.
    ss.
    all:cycle 1.
    eapply DSameK.
    all:cycle 1.
    boom.
    (*Now we have a collection of gap-only evar goals.  We can start by
    solving those with a single evar:*)
    5:boom_internal true.
    (*which creates others with a single evar:*)
    4:boom.
    (*The remainder all have at least two gap evars.  Probably best to solve
    them all together to enable backtracking:*)
    all:[>boom_internal true..].
  - minlines.
    destruct (gofis t2_1 false); dintros.
    + rootify d0.
      eapply Delout.
      node.
      boom.
      boom.
      gap.
      force exact t2_1.
      boom.
      rootify d.
      node.
      boom.
      boom.
      force exact t2_2.
      boom_internal true. (**)
      boom.
      force exact t.
      boom.
      ss.
      boom.
      ss.
      boom.
      eapply DSameK.
      boom.
      boom.
    + rootify d1.
      eapply Delout.
      node.
      boom.
      boom.
      node.
      boom.
      boom.
      gap.
      force exact t2_1.
      boom.
      force exact w1.
      boom_internal true.
      ss.
      boom.
      boom.
      node.
      boom.
      boom.
      force exact w2.
      boom_internal true.
      boom.
      gap.
      force exact t.
      boom_internal true.
      ss.
      boom.
      ss.
      boom_internal true.
      eapply DSameK.
      boom.
      boom.
Qed.

Inductive delminResult(k : EZ)(g : EB)(f : EL) : Set :=
| NoMin(eqf : f = [])
| MinDeleted(min : A)`(eqf : f = ^min ++ rf)(dr : delpair k g rf).

Definition delmin`(t : wavltree k g lg rg f) : delminResult k g f.
Proof.
  induction t; dintros.
  - eapply NoMin.
    reflexivity.
  - minlines.
    clear IHt2.
    destruct IHt1; dintros.
    + eapply MinDeleted.
      rewrite Eapp_nil_l.
      reflexivity.
      eapply Delout.
      gap.
      force exact t2.
      eapply DLowerK.
      boom.
      boom.
    + onhead delpair destr.
      onhead deletedHow destr; dintros.
      * eapply MinDeleted.
        assoc 0.
        reflexivity.
        eapply Delout.
        node.
        boom.
        boom.
        force exact t.
        boom.
        force exact t2.
        boom.
        ss.
        boom.
        eapply DSameK.
        boom.
        boom.
      * destruct (gofis t2 false); dintros.
        -- destruct (gofis t1 true); dintros.
           ++ destruct (tryLowering t2); dintros.
              ** eapply MinDeleted.
                 assoc 0.
                 reflexivity.
                 eapply drot1.
                 force exact t.
                 boom.
                 force exact t2.
                 boom.
                 ss.
                 assumption.
              ** eapply MinDeleted.
                 assoc 0.
                 reflexivity.
                 eapply Delout.
                 node.
                 boom.
                 boom.
                 force exact t.
                 boom.
                 force exact t'.
                 boom.
                 ss.
                 boom.
                 eapply DLowerK.
                 boom.
                 boom.
           ++ eapply MinDeleted.
              assoc 0.
              reflexivity.
              eapply Delout.
              node.
              boom.
              boom.
              force exact t.
              boom.
              force exact t2.
              boom.
              ss.
              boom.
              eapply DSameK.
              boom.
              boom.
        -- unerase_gaps.
           eapply MinDeleted.
           assoc 0.
           reflexivity.
           eapply Delout.
           node.
           boom.
           boom.
           gap.
           force exact t.
           boom.
           gap.
           force exact t2.
           boom_internal true. (**)
           ss.
           boom.
           eapply DLowerK.
           boom.
           boom.
Qed.

Inductive delmaxResult(k : EZ)(g : EB)(f : EL) : Set :=
| NoMax(eqf : f = [])
| MaxDeleted(max : A)`(eqf : f = lf ++ ^max)(dr : delpair k g lf).

Definition delmax`(t : wavltree k g lg rg f) : delmaxResult k g f.
Proof.
  induction t; dintros.
  - eapply NoMax.
    reflexivity.
  - clear IHt1.
    destruct IHt2; dintros.
    + eapply MaxDeleted.
      rewrite Eapp_nil_r.
      reflexivity.
      eapply Delout.
      gap.
      force exact t1.
      eapply DLowerK.
      boom.
      boom.
    + onhead delpair destr.
      onhead deletedHow destr; dintros.
      * eapply MaxDeleted.
        assoc 2.
        reflexivity.
        eapply Delout.
        node.
        boom.
        boom.
        force exact t1.
        boom.
        force exact t.
        boom.
        ss.
        boom.
        eapply DSameK.
        boom.
        boom.        
      * destruct (gofis t1 false); dintros.
        -- destruct (gofis t2 true); dintros.
           ++ destruct (tryLowering t1); dintros.
              ** eapply MaxDeleted.
                 assoc 2.
                 reflexivity.
                 eapply drot2.
                 force exact t1.
                 boom.
                 force exact t.
                 boom.
                 ss.
                 assumption.
              ** eapply MaxDeleted.
                 assoc 2.
                 reflexivity.
                 eapply Delout.
                 node.
                 boom.
                 boom.
                 force exact t'.
                 boom.
                 force exact t.
                 boom.
                 ss.
                 boom.
                 eapply DLowerK.
                 boom.
                 boom.
           ++ eapply MaxDeleted.
              assoc 2.
              reflexivity.
              eapply Delout.
              node.
              boom.
              boom.
              force exact t1.
              boom.
              force exact t.
              boom.
              ss.
              boom.
              eapply DSameK.
              boom.
              boom.
        -- unerase_gaps.
           eapply MaxDeleted.
           assoc 2.
           reflexivity.
           eapply Delout.
           node.
           boom.
           boom.
           gap.
           force exact t1.
           boom.
           gap.
           force exact t.
           all:cycle 1.
           ss.
           all:cycle 1.
           eapply DLowerK.
           boom_internal true.
           boom.
           boom_internal true.
           boom.
Qed.

Inductive deleteResult(x : A)(k : EZ)(g : EB)(f : EL) : Set :=
| Deleted`(eqf : f = f1 ++ ^x ++ f2)(dr : delpair k g (f1 ++ f2))
| DNotFound(ni : ENotIn x f).

Definition delete(x : A)`(t : wavltree k g lg rg f) : deleteResult x k g f.
Proof.
  induction t; dintros.
  - eapply DNotFound.
    ss.
  - destruct (compare_spec x d); dintros.
    + destruct (gofis t2 false); dintros.
      * destruct (delmin t2); dintros.
        -- eapply Deleted.
           reflexivity.
           eapply Delout.
           force exact t1.
           rewrite Eapp_nil_r.
           reflexivity.
           eapply DSameK.
           boom.
           boom.
        -- onhead delpair destr.
           onhead deletedHow destr; dintros.
           ** eapply Deleted.
              reflexivity.
              eapply Delout.
              node.
              boom.
              boom.
              force exact t1.
              boom.
              force exact t.
              boom.
              ss.
              boom.
              eapply DSameK.
              boom.
              boom.
           ** destruct (isMissing t1); dintros.
              --- eapply Deleted.
                  reflexivity.
                  eapply Delout.
                  node.
                  boom.
                  boom.
                  missing.
                  reflexivity.
                  boom.
                  boom.
                  boom.
                  boom.
                  gap.
                  force exact t.
                  boom_internal true.
                  ss.
                  boom_internal true.
                  eapply DLowerK.
                  boom.
                  boom.
              --- eapply Deleted.
                  reflexivity.
                  eapply Delout.
                  node.
                  boom.
                  boom.
                  force exact t1.
                  boom.
                  force exact t.
                  boom.
                  ss.
                  boom.
                  eapply DSameK.
                  boom.
                  boom.
      * destruct (delmax t1); dintros.
        -- eapply Deleted.
           reflexivity.
           eapply Delout.
           rewrite Eapp_nil_l.
           gap.
           force exact t2.
           eapply DLowerK.
           boom.
           boom.
        -- onhead delpair destr.
           onhead deletedHow destr; dintros.
           ++ eapply Deleted.
              reflexivity.
              eapply Delout.
              rootify max.
              node.
              boom.
              boom.
              force exact t.
              boom.
              force exact t2.
              boom.
              ss.
              boom.
              eapply DSameK.
              boom.
              boom.
           ++ unerase_gaps.
              eapply Deleted.
              reflexivity.
              eapply Delout.
              rootify max.
              node.
              boom.
              boom.
              gap.
              force exact t.
              boom.
              gap.
              force exact t2.
              boom_internal true. (**)
              ss.
              boom.
              eapply DLowerK.
              boom.
              boom.
    + clear IHt2.
      destruct IHt1; dintros.
      * onhead delpair destr.
        onhead deletedHow destr; dintros.
        -- eapply Deleted.
           rootify x.
           reflexivity.
           eapply Delout.
           rootify d.
           node.
           boom.
           boom.
           force exact t.
           boom.
           force exact t2.
           boom.
           ss.
           boom.
           eapply DSameK.
           boom.
           boom.
        -- unerase_gaps.
           destruct lg; dintros.
           ++ unerase_gaps.
              destruct rg; dintros.
              ** eapply Deleted.
                 rootify x.
                 reflexivity.
                 eapply Delout.
                 rootify d.
                 node.
                 boom.
                 boom.
                 force exact t.
                 boom.
                 gap.
                 force exact t2.
                 boom_internal true.
                 ss.
                 boom.
                 eapply DLowerK.
                 boom.
                 boom.
              ** destruct (tryLowering t2); dintros.
                 --- eapply Deleted.
                     rootify x.
                     reflexivity.
                     rootify d.
                     eapply drot1.
                     force exact t.
                     boom.
                     force exact t2.
                     boom.
                     ss.
                     assumption.
                 --- eapply Deleted.
                     rootify x.
                     reflexivity.
                     eapply Delout.
                     rootify d.
                     node.
                     boom.
                     boom.
                     force exact t.
                     boom.
                     force exact t'.
                     boom.
                     ss.
                     boom.
                     eapply DLowerK.
                     boom.
                     boom.
           ++ destruct (isMissing t2); dintros.
              ** eapply Deleted.
                 rootify x.
                 reflexivity.
                 eapply Delout.
                 rootify d.
                 node.
                 boom.
                 boom.
                 gap.
                 force exact t.
                 boom.
                 missing.
                 reflexivity.
                 boom_internal true.
                 boom.
                 boom.
                 ss.
                 boom_internal true.
                 eapply DLowerK.
                 boom.
                 boom.
              ** eapply Deleted.
                 rootify x.
                 reflexivity.
                 eapply Delout.
                 rootify d.
                 node.
                 boom.
                 boom.
                 force exact t.
                 boom.
                 force exact t2.
                 boom.
                 ss.
                 boom.
                 eapply DSameK.
                 boom.
                 boom.
      * eapply DNotFound.
        ss.
    + clear IHt1.
      destruct IHt2; dintros.
      * onhead delpair destr.
        onhead deletedHow destr; dintros.
        -- eapply Deleted.
           rootify x.
           reflexivity.
           eapply Delout.
           rootify d.
           node.
           boom.
           boom.
           force exact t1.
           boom.
           force exact t.
           boom.
           ss.
           boom.
           eapply DSameK.
           boom.
           boom.
        -- unerase_gaps.
           destruct rg; dintros.
           ++ unerase_gaps.
              destruct lg; dintros.
              ** eapply Deleted.
                 rootify x.
                 reflexivity.
                 eapply Delout.
                 rootify d.
                 node.
                 boom.
                 boom.
                 gap.
                 force exact t1.
                 boom.
                 force exact t.
                 boom_internal true.
                 ss.
                 boom.
                 eapply DLowerK.
                 boom.
                 boom.
              ** destruct (tryLowering t1); dintros.
                 --- eapply Deleted.
                     rootify x.
                     reflexivity.
                     rootify d.
                     eapply drot2.
                     force exact t1.
                     boom.
                     force exact t.
                     boom.
                     ss.
                     assumption.
                 --- eapply Deleted.
                     rootify x.
                     reflexivity.
                     eapply Delout.
                     rootify d.
                     node.
                     boom.
                     boom.
                     force exact t'.
                     boom.
                     force exact t.
                     boom.
                     ss.
                     boom.
                     eapply DLowerK.
                     boom.
                     boom.
           ++ destruct (isMissing t1); dintros.
              ** eapply Deleted.
                 rootify x.
                 reflexivity.
                 eapply Delout.
                 rootify d.
                 node.
                 boom.
                 boom.
                 missing.
                 reflexivity.
                 boom.
                 boom.
                 boom.
                 boom.
                 gap.
                 force exact t.
                 boom_internal true.
                 ss.
                 boom_internal true.
                 eapply DLowerK.
                 boom.
                 boom.
              ** eapply Deleted.
                 rootify x.
                 reflexivity.
                 eapply Delout.
                 rootify d.
                 node.
                 boom.
                 boom.
                 force exact t1.
                 boom.
                 force exact t.
                 boom.
                 ss.
                 boom.
                 eapply DSameK.
                 boom.
                 boom.
      * eapply DNotFound.
        ss.
Qed.

(* End Wavltree. *)

Set Printing Width 120.

Extract Inductive delpair => "( * )" [ "" ].

Extraction Inline negb.

Extraction "wavl-noindex-noauto.ml" find insert delete.
