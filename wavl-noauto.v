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

Require Import elist.
Require Import ezbool.
Require Import utils.
Require Import hypiter.

Generalizable All Variables.

Context {A : Set}.

Context {ordA : Ordered A}.

Notation "x =<> y" := (compare_spec x y) (at level 70, only parsing).

Notation EL := ##(list A).
Notation EZ := ##Z.
Notation EB := ##bool.

Open Scope E_scope.

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

Tactic Notation "??" constr(H) :=
  (tryif (is_var H; try (clear H;
                         fail 1))
    then case_eq H
    else case H);
  dintros.

Tactic Notation "??" constr(H) "on" constr(H') :=
  case H with (1:=H'); dintros.

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

(**********************************************************************)

Section Lemmas.
  
  Lemma wavl_min_rank`(w : wavltree k g lg rg c) : k >= - #1.
  Proof.
    induction w.
    boom.
    boom.
  Qed.
  
  Lemma wavl_node_min_rank`(w : wavltree k g lg rg c) : c <> [] -> k >= #0.
  Proof.
    ?? w.
    pose proof (wavl_min_rank (left_child w)). boom.
    boom.
  Qed.
  
  Lemma wavl_node_nonempty`(w : wavltree k g lg rg c) : k >= #0 -> c <> [].
  Proof.
    ?? w.
    boom.
    boom.
  Qed.
  
  Lemma missing_contents`(w : wavltree (- #1) g lg rg c) : c = [].
  Proof.
    pose proof (wavl_node_min_rank w).
    ?? w.
    boom.
    reflexivity.
  Qed.

  Lemma missing_rank`(w : wavltree k g lg rg []) : k = - #1.
  Proof.
    ?? w.
    fnenil.
    reflexivity.
  Qed.
  
  Lemma wavl_is_sorted`(w : wavltree k g lg rg c) : Esorted c.
  Proof.
    ?? w.
    assumption.
    repeat econstructor.
  Qed.

End Lemmas.

Ltac bang_setup_tactic ::=
  let f H :=
      (lazymatch type of H with
       | wavltree _ _ _ _ _ =>
         first [apply missing_contents in H
               |apply missing_rank in H
               |apply wavl_node_min_rank in H; [|assumption||fnenil]
               |apply wavl_min_rank in H]
       | _ => idtac
       end) in
  hyps => loop f.

Ltac ss_setup_tactic :=
  let f H := (try apply wavl_is_sorted in H) in
  hyps => loop f.

Ltac ss := ss_setup_tactic; unerase; solve[solve_sorted].

(**********************************************************************)

Section Check_Leaf_Rule. 

  Local Set Asymmetric Patterns.

  Local Definition is_leaf`(w : wavltree k g lg rg c) : bool :=
    match w with
    | Node _ _ _ _ _ _ _ _ (Missing _ _ _ _) _ _ (Missing _ _ _ _) _ _ => true
    | _ => false
    end.

  Ltac destruct_match :=
    match goal with |- context[match ?X with _ => _ end] => destruct X end.

  Local Lemma leaf_rule_works`(w : wavltree k g lg rg c) : k = #0 <-> is_leaf w = true.
  Proof.
    unfold is_leaf.
    repeat destruct_match.
    all: [>boom..].
  Qed.

End Check_Leaf_Rule.

(**********************************************************************)

Section Find.

  Inductive findResult(x : A)(c : EL) : Set :=
  | Found`(_: c = lc++[x]++rc)
  | NotFound(_: ENotIn x c).

  Fixpoint find(x : A)`(w : wavltree k g lg rg c) : findResult x c.
  Proof.
    ?? w.
    - ?? (x =<> (datum w)).
      + eapply Found. reflexivity.
      + ?? (find x) on (left_child w).
        * eapply Found. rootify x. reflexivity.
        * eapply NotFound. ss.
      + ?? (find x) on (right_child w).
        * eapply Found. rootify x. reflexivity.
        * eapply NotFound. ss.
    - eapply NotFound. ss.
  Qed.

End Find.

Section SetGap.

  Definition setgap`(w : wavltree k ig lg rg c)(og : bool) : wavltree k #og lg rg c.
  Proof.
    ?? w.
    - eapply Node. reflexivity. reflexivity. all:eassumption.
    - eapply Missing. all:reflexivity.
  Qed.

End SetGap.

Section GetGap.

  Definition getgap`(w : wavltree k g lg rg c) : { g' | c <> [] -> #g' = g}.
  Proof.
    ?? w.
    - eexists. reflexivity.
    - exists false. boom.
  Qed.

  Definition getgap2`(w : wavltree k g lg rg c) : { g' | k >= #0 -> #g' = g}.
  Proof.
    ?? w.
    - eexists. reflexivity.
    - exists false. boom.
  Qed.

End GetGap.

Section IsGap.

  Notation "x ?= y" := (Bool.bool_dec x y) (only parsing).

  Definition isgap`(w : wavltree k g lg rg c)(g' : bool) : {k >= #0 /\ #g' = g} + {k= - #1 \/ #g' <> g}.
  Proof.
    ?? w.
    - ?? (g' ?= (gap w)).
      + left. boom.
      + right. boom.
    - right. boom.
  Qed.

End IsGap.

Section IsMissing.

  Definition isMissing`(w : wavltree k g lg rg c) : {c = [] /\ k = - #1} + {c <> [] /\ k >= #0}.
  Proof.
    ?? w.
    - right. boom.
    - left. boom.
    Qed.

End IsMissing.

Ltac start_node := eapply Node; [reflexivity|reflexivity|..].
Ltac missing := eapply Missing; [reflexivity|boom|reflexivity|reflexivity].
Ltac use w := force refine w by boom.
Ltac use_regap w := force refine (setgap w _) by boom.
Ltac finish :=
  match goal with
  | |- Esorted _ => ss
  | _ => boom
  end.

Section Insert_Rotations.

  Definition irot1`(lw : wavltree k #false llg lrg lc)(x : A)`(rw : wavltree (k - #2) #true rlg rrg rc)
    : llg = Enegb lrg -> Esorted(lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc).
  Proof.
    ?? lw.
    - ?? (right_child lw).
      + ?? (gap (right_child lw)).
        * rootify d. start_node. use lw0.
          rootify x. start_node. use_regap rw0. use_regap rw. all:finish.
        * rootify d0. start_node. start_node. use_regap lw0. use lw1. finish. finish.
          start_node. use rw1. use_regap rw. all:finish.
      + assert (k = #1) as -> by boom. rsimp. apply missing_contents in rw as ->.
        rootify d. start_node. use lw0. start_node. missing. missing. all:finish.
    - boom.
  Qed.

  Definition irot2`(lw : wavltree (k - #2) #true llg lrg lc)(x : A)`(rw : wavltree k #false rlg rrg rc)
    : Enegb rlg = rrg -> Esorted(lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc).
  Proof.
    ?? rw.
    - ?? (left_child rw).
      + ?? (gap (left_child rw)).
        * rootify d. start_node. start_node. use_regap lw. use_regap lw0. finish. finish.
          use rw0. all:finish.
        * rootify d0. start_node. start_node. use_regap lw. use lw1. finish. finish.
          start_node. use rw1. use_regap rw0. all:finish.
      + assert (k = #1) as -> by boom. rsimp. apply missing_contents in lw as ->.
        rootify d. start_node. start_node. missing. missing. finish. finish.
        use rw0. all:finish.
    - boom.
  Qed.

End Insert_Rotations.

Ltac unerase_gaps :=
  subst;
  let f H :=
      try
        lazymatch type of H with
          wavltree _ ?G _ _ _ =>
          is_var G;
          case (getgap H);
          let X := fresh in
          let G' := fresh in
          intros G' X;
          first [specialize (X ltac:(assumption||fnenil))
                |specialize (X (wavl_node_nonempty H ltac:(boom)))];
          rewrite <-X in *;
          clear X G;
          rename G' into G
        end in
    hyps => loop f.

Section Insert.

  Inductive insertedHow(ik ok : EZ)(ig og olg org : EB) : Set :=
  | ISameK(_: ok = ik)(_: og = ig)
  | IWasMissing(_: ik = - #1)(_: ok = #0)(_: og = #false)
  | IHigherK(_: ik >= #0)(_: ok = ik + #1)(_: olg = Enegb org)(_: og = #false).

  Inductive insertResult(x: A)(k : EZ)(g lg rg : EB)(c : EL) : Set :=
  | Inserted`(_: c = lc++rc)
            `(ow: wavltree ok og olg org (lc++[x]++rc))
            `(_: insertedHow k ok g og olg org)
  | FoundByInsert`(_: c = lc++[x]++rc).
  
  Lemma nilnilnil : [] = [] ++ [] :> EL.
  Proof.
    rewrite Eapp_nil_l.
    reflexivity.
  Qed.

  Fixpoint insert(x : A)`(w : wavltree k g lg rg c) : insertResult x k g lg rg c.
  Proof.
    ?? w.
    - ?? (x =<> (datum w)).
      + eapply FoundByInsert. reflexivity.
      + ?? (insert x) on (left_child w).
        * ?? (pick insertedHow).
          -- reassoc. eapply Inserted. reflexivity.
             rootify d. start_node. use ow. use rw. finish. finish.
             eapply ISameK. boom. boom.
          -- ?? (isMissing (right_child w)).
             ++ reassoc. eapply Inserted. reflexivity.
                rootify d. start_node. use ow. missing. finish. finish.
                eapply IHigherK. boom. boom. boom. boom.
             ++ reassoc. eapply Inserted. reflexivity.
                rootify d. start_node. use ow. use rw. finish. finish.
                eapply ISameK. boom. boom.
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ reassoc. eapply Inserted. reflexivity.
                rootify d. start_node. use ow. use rw. finish. finish.
                eapply ISameK. boom. boom.
             ++ ?? (isgap (right_child w) false).
                ** reassoc. eapply Inserted. reflexivity.
                   rootify d. start_node. use ow. use_regap rw. finish. finish.
                   eapply IHigherK. boom. boom. boom. boom.
                ** reassoc. eapply Inserted. reflexivity.
                   rootify d. eapply irot1. use ow. use rw. finish. finish.
                   eapply ISameK. boom. boom.
        * rootify x. eapply FoundByInsert. reflexivity.
      + ?? (insert x) on (right_child w).
        * ?? (pick insertedHow).
          -- assoc 2. eapply Inserted. reflexivity.
             rootify d. start_node. use lw. use ow. finish. finish.
             eapply ISameK. boom. boom.
          -- ?? (isMissing (left_child w)).
             ++ assoc 2. eapply Inserted. reflexivity.
                rootify d. start_node. missing. use ow. finish. finish.
                eapply IHigherK. boom. boom. boom. boom.
             ++ assoc 2. eapply Inserted. reflexivity.
                rootify d. start_node. use lw. use ow. finish. finish.
                eapply ISameK. boom. boom.
          -- unerase_gaps. ?? (gap (right_child w)).
             ++ assoc 2. eapply Inserted. reflexivity.
                rootify d. start_node. use lw. use ow. finish. finish.
                eapply ISameK. boom. boom.
             ++ ?? (isgap (left_child w) false).
                ** assoc 2. eapply Inserted. reflexivity.
                   rootify d. start_node. use_regap lw. use ow. finish. finish.
                   eapply IHigherK. boom. boom. boom. boom.
                ** assoc 2. eapply Inserted. reflexivity.
                   rootify d. eapply irot2. use lw. use ow. finish. finish.
                   eapply ISameK. boom. boom.
        * rootify x. eapply FoundByInsert. reflexivity.
    - eapply Inserted. eapply nilnilnil.
      start_node. missing. missing. finish. finish.
      eapply IWasMissing. boom. boom. boom.
  Qed.

End Insert.

(**********************************************************************)

Section TryLowering.

  Inductive tryLoweringResult(k : EZ)(g lg rg : EB)(c : EL) : Set :=
  | TLlowered(_: lg = #true)(_: rg = #true)(ow: wavltree (k - #1) g #false #false c)
  | TLtooLow(_: lg = #false \/ rg = #false).

  Definition tryLowering`(w : wavltree k g lg rg c) : tryLoweringResult k g lg rg c.
  Proof.
    ?? w.
    - ?? (isgap (left_child w) true).
      + ?? (isgap (right_child w) true).
        * eapply TLlowered. reflexivity. reflexivity.
          start_node. use_regap lw. use_regap rw. finish. finish.
        * eapply TLtooLow. boom.
      + eapply TLtooLow. boom.
    - eapply TLtooLow. boom.
  Qed.

End TryLowering.

Inductive deletedHow(ik ok : EZ)(ig og : EB) : Set :=
| DSameK(_: ok = ik)(_: og = ig)
| DLowerK(_:  ok = ik - #1)(_: og = #true).

Inductive delpair(k : EZ)(g : EB)(c : EL) : Set :=
| Delout`(dh : deletedHow k ok g og)`(ow : wavltree ok og olg org c).

Section Delete_Rotations.

  Definition drot1`(lw : wavltree (k - #3) #true llg lrg lc)(x : A)`(rw : wavltree (k - #1) #false rlg rrg rc)
    : rlg = #false \/ rrg = #false -> Esorted(lc++[x]++rc) -> forall g, delpair k #g (lc++[x]++rc).
  Proof.
    ?? rw.
    - ?? (left_child rw).
      + ?? (isgap (right_child rw) false).
        * eapply Delout. apply DSameK. reflexivity. reflexivity.
          rootify d. start_node. start_node. use lw. use lw0. finish. finish. use_regap rw0. finish. finish.
        * eapply Delout. apply DSameK. reflexivity. reflexivity.
          rootify d0. start_node. start_node. use_regap lw. use lw1. finish. finish.
          start_node. use rw1. use_regap rw0. all:finish.
      + assert (k = #2) as -> by boom. rsimp. apply missing_contents in lw as ->.
        eapply Delout. apply DSameK. reflexivity. reflexivity.
        rootify d. start_node. start_node. missing. missing. finish. finish. use_regap rw0. all:finish.
    - boom.
  Qed.

  Definition drot2`(lw : wavltree (k - #1) #false llg lrg lc)(x : A)`(rw : wavltree (k - #3) #true rlg rrg rc)
    : llg = #false \/ lrg = #false -> Esorted(lc++[x]++rc) -> forall g, delpair k #g (lc++[x]++rc).
  Proof.
    ?? lw.
    - ?? (right_child lw).
      + ?? (isgap (left_child lw) false).
        * eapply Delout. apply DSameK. reflexivity. reflexivity.
          rootify d. start_node. use_regap lw0.
          rootify x. start_node. use rw0. use rw. all:finish.
        * eapply Delout. apply DSameK. reflexivity. reflexivity.
          rootify d0. start_node. start_node. use_regap lw0. use lw1. finish. finish.
          start_node. use rw1. use_regap rw. all:finish.
      + assert (k = #2) as -> by boom. rsimp. apply missing_contents in rw as ->.
        eapply Delout. apply DSameK. reflexivity. reflexivity.
        rootify d. start_node. use_regap lw0. start_node. missing. missing. all:finish.
    - boom.
  Qed.

End Delete_Rotations.

Section Delete_Minimum.

  Inductive delminResult(k : EZ)(g : EB)(c : EL) : Set :=
    MinDeleted(min : A)`(_: c = [min]++rc)(dp : delpair k g rc).

  Fixpoint delmin`(w : wavltree k g lg rg c) : k >= #0 -> delminResult k g c.
  Proof.
    ?? w.
    - ?? (isMissing (left_child w)).
      + eapply MinDeleted. rewrite Eapp_nil_l. reflexivity.
        eapply Delout. apply DLowerK. reflexivity. reflexivity.
        use_regap rw.
      + ?? delmin on (left_child w). boom. ?? (pick delpair). ?? (pick deletedHow).
        * eapply MinDeleted. reassoc. reflexivity.
          eapply Delout. apply DSameK. reflexivity. reflexivity.
          start_node. use ow. use rw. all:finish.
        * ?? (isgap (right_child w) false).
          -- ?? (isgap (left_child w) true).
             ++ ?? (tryLowering (right_child w)).
                ** eapply MinDeleted. reassoc. reflexivity.
                   eapply Delout. apply DLowerK. reflexivity. reflexivity.
                   start_node. use ow. use ow0. all:finish.
                ** eapply MinDeleted. reassoc. reflexivity.
                   eapply drot1. use ow. use rw. all:finish.
             ++ eapply MinDeleted. reassoc. reflexivity.
                eapply Delout. apply DSameK. reflexivity. reflexivity.
                start_node. use ow. use rw. all:finish.
          -- unerase_gaps.
             eapply MinDeleted. reassoc. reflexivity.
             eapply Delout. apply DLowerK. reflexivity. reflexivity.
             start_node. use_regap ow. use_regap rw. all:finish.
    - boom.
  Qed.

End Delete_Minimum.

Section Delete_Maximum.

  Inductive delmaxResult(k : EZ)(g : EB)(c : EL) : Set :=
   MaxDeleted(max : A)`(_: c = lc++[max])(dp : delpair k g lc).

  Fixpoint delmax`(w : wavltree k g lg rg c) : k >= #0 -> delmaxResult k g c.
  Proof.
    ?? w.
    - ?? (isMissing (right_child w)).
      + eapply MaxDeleted. rewrite Eapp_nil_r. reflexivity.
        eapply Delout. apply DLowerK. reflexivity. reflexivity.
        use_regap lw.
      + ?? delmax on (right_child w). boom. ?? (pick delpair). ?? (pick deletedHow).
        * eapply MaxDeleted. assoc 2. reflexivity.
          eapply Delout. apply DSameK. reflexivity. reflexivity.
          start_node. use lw. use ow. all:finish.
        * ?? (isgap (left_child w) false).
          -- ?? (isgap (right_child w) true).
             ++ ?? (tryLowering (left_child w)).
                ** eapply MaxDeleted. assoc 2. reflexivity.
                   eapply Delout. apply DLowerK. reflexivity. reflexivity.
                   start_node. use ow0. use ow. all:finish.
                ** eapply MaxDeleted. assoc 2. reflexivity.
                   eapply drot2. use lw. use ow. all:finish.
             ++ eapply MaxDeleted. assoc 2. reflexivity.
                eapply Delout. apply DSameK. reflexivity. reflexivity.
                start_node. use lw. use ow. all:finish.
          -- unerase_gaps. eapply MaxDeleted. assoc 2. reflexivity.
             eapply Delout. apply DLowerK. reflexivity. reflexivity.
             start_node. use_regap lw. use_regap ow. all:finish.
    - boom.
  Qed.

End Delete_Maximum.

Section Delete.

  Inductive deleteResult(x : A)(k : EZ)(g : EB)(c : EL) : Set :=
  | Deleted`(_: c = lc++[x]++rc)(dp : delpair k g (lc++rc))
  | DNotFound(_: ENotIn x c).

  Fixpoint delete(x : A)`(w : wavltree k g lg rg c) : deleteResult x k g c.
  Proof.
    ?? w.
    - ?? (x =<> (datum w)).
      + ?? (isMissing (left_child w)).
        * eapply Deleted. reflexivity.
          eapply Delout. apply DLowerK. reflexivity. reflexivity.
          rewrite Eapp_nil_l. use_regap rw.
        * ?? (isMissing (right_child w)).
          -- eapply Deleted. reflexivity.
             eapply Delout. apply DLowerK. reflexivity. reflexivity.
             rewrite Eapp_nil_r. use_regap lw.
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ ?? (delmin (right_child w)). boom. ?? (pick delpair). ?? (pick deletedHow).
                ** eapply Deleted. reflexivity.
                   eapply Delout. apply DSameK. reflexivity. reflexivity.
                   start_node. use lw. use ow. all:finish.
                ** eapply Deleted. reflexivity.
                   eapply Delout. apply DLowerK. reflexivity. reflexivity.
                   start_node. use_regap lw. use_regap ow. all:finish.
             ++ ?? (delmax (left_child w)). boom. ?? (pick delpair). ?? (pick deletedHow).
                ** eapply Deleted. reflexivity.
                   eapply Delout. apply DSameK. reflexivity. reflexivity.
                   assoc 0. start_node. use ow. use rw. all:finish.
                ** eapply Deleted. reflexivity.
                   eapply Delout. apply DSameK. reflexivity. reflexivity.
                   assoc 0. start_node. use ow. use rw. all:finish.
      + ?? (delete x) on (left_child w).
        * ?? (pick delpair). ?? (pick deletedHow).
          -- eapply Deleted. rootify x. reflexivity.
             eapply Delout. apply DSameK. reflexivity. reflexivity.
             rootify d. start_node. use ow. use rw. all:finish.
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ unerase_gaps. ?? (gap (right_child w)).
                ** eapply Deleted. rootify x. reflexivity.
                   eapply Delout. apply DLowerK. reflexivity. reflexivity.
                   rootify d. start_node. use ow. use_regap rw. all:finish.
                ** ?? (tryLowering (right_child w)).
                   --- eapply Deleted. rootify x. reflexivity.
                       eapply Delout. apply DLowerK. reflexivity. reflexivity.
                       rootify d. start_node. use ow. use ow0. all:finish.
                   --- eapply Deleted. rootify x. reflexivity.
                       rootify d. eapply drot1. use ow. use rw. all:finish.
             ++ ?? (isMissing (right_child w)).
                ** eapply Deleted. rootify x. reflexivity.
                   rootify d. eapply Delout. apply DLowerK. reflexivity. reflexivity.
                   start_node. use_regap ow. missing. all:finish.
                ** eapply Deleted. rootify x. reflexivity.
                   eapply Delout. apply DSameK. reflexivity. reflexivity.
                   rootify d. start_node. use ow. use rw. all:finish.
        * eapply DNotFound. ss.
      + ?? (delete x) on (right_child w).
        * ?? (pick delpair). ?? (pick deletedHow).
          -- eapply Deleted. rootify x. reflexivity.
             rootify d. eapply Delout. apply DSameK. reflexivity. reflexivity.
             start_node. use lw. use ow. all:finish.
          -- unerase_gaps. ?? (gap (right_child w)).
             ++ unerase_gaps. ?? (gap (left_child w)).
                ** eapply Deleted. rootify x. reflexivity.
                   rootify d. eapply Delout. apply DLowerK. reflexivity. reflexivity.
                   start_node. use_regap lw. use ow. all:finish.
                ** ?? (tryLowering (left_child w)).
                   --- eapply Deleted. rootify x. reflexivity.
                       rootify d. eapply Delout. apply DLowerK. reflexivity. reflexivity.
                       start_node. use ow0. use ow. all:finish.
                   --- eapply Deleted. rootify x. reflexivity.
                       rootify d. eapply drot2. use lw. use ow. all:finish.
             ++ ?? (isMissing (left_child w)).
                ** eapply Deleted. rootify x. reflexivity.
                   rootify d. eapply Delout. apply DLowerK. reflexivity. reflexivity.
                   start_node. missing. use_regap ow. all:finish.
                ** eapply Deleted. rootify x. reflexivity.
                   rootify d. eapply Delout. apply DSameK. reflexivity. reflexivity.
                   start_node. use lw. use ow. all:finish.
        * eapply DNotFound. ss.
    - eapply DNotFound. ss.
  Qed.

End Delete.

Set Printing Width 120.

Require Import ExtrOcamlBasic.

Extract Inductive delpair => "( * )" [ "" ].
Extract Inductive delminResult => "( * )" [ "" ].
Extract Inductive delmaxResult => "( * )" [ "" ].

Extraction Inline negb.

Extract Inlined Constant Bool.bool_dec => "(=)".

Extraction "wavl-noauto.ml" find insert delete.
