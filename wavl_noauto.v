
(*** Weak AVL Trees ***)

(*+ 
See "Rank-Balanced Trees" by Haeupler, Sen, Tarjan
[http://www.cs.princeton.edu/~sssix/papers/rb-trees-talg.pdf].
*)

(* A non-automated (actually, semi-automated) version of wavl.v, with no
tailored specific solver tactics.  Note that the general "boom" and "ss"
automation tactics are still used throughout. *)
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

Ltac left_child w := idtac;
  lazymatch type of w with
    wavltree _ _ _ _ (?C++[_]++_) =>
    lazymatch goal with
      L:wavltree _ _ _ _ C |- _ => L
    end
  end.

Notation "'left_child' w" := ltac:(just left_child w)
                                    (at level 199, no associativity, only parsing).

Ltac right_child w := idtac;
  lazymatch type of w with
    wavltree _ _ _ _ (_++[_]++?C) =>
    lazymatch goal with
      R:wavltree _ _ _ _ C |- _ => R
    end
  end.

Notation "'right_child' w" := ltac:(just right_child w)
                                     (at level 199, no associativity, only parsing).

Ltac datum w := idtac;
  lazymatch type of w with
    wavltree _ _ _ _ (_++[?D]++_) => D
  end.

Notation "'datum' w" := ltac:(just datum w)
                               (at level 199, no associativity, only parsing).

Ltac gap w := idtac;
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
    induction w. boom.
  Qed.
  
  Lemma wavl_node_min_rank`(w : wavltree k g lg rg c) : c <> [] -> k >= #0.
  Proof.
    ?? w. 1: pose proof (wavl_min_rank (left_child w)). boom.
  Qed.
  
  Lemma wavl_node_nonempty`(w : wavltree k g lg rg c) : k >= #0 -> c <> [].
  Proof.
    ?? w. boom.
  Qed.
  
  Lemma missing_contents`(w : wavltree (- #1) g lg rg c) : c = [].
  Proof.
    pose proof (wavl_node_min_rank w) as H.
    ?? w. boom.
  Qed.

  Lemma missing_rank`(w : wavltree k g lg rg []) : k = - #1.
  Proof.
    ?? w.
    - fnenil.
    - reflexivity.
  Qed.
  
  Lemma wavl_is_sorted`(w : wavltree k g lg rg c) : Esorted c.
  Proof.
    ?? w.
    - assumption.
    - repeat econstructor.
  Qed.

End Lemmas.

Ltac allhyps tac := idtac;
  lazymatch goal with
  | H : _ |- _ => tac H; revert H; allhyps tac; intro H
  | _ => idtac
  end.

Ltac bang_setup_tactic ::= idtac;
  let f H :=
      (lazymatch type of H with
       | wavltree _ _ _ _ _ =>
         first [apply missing_rank in H
               |apply wavl_node_min_rank in H; [|assumption||fnenil]
               |apply wavl_min_rank in H]
       | _ => idtac
       end) in
  allhyps f.

Ltac ss_setup_tactic := idtac;
  let f H := (try apply wavl_is_sorted in H) in
  allhyps f.

Ltac ss := ss_setup_tactic; unerase; solve[solve_sorted].

(**********************************************************************)

Section Check_Leaf_Rule. 

  Local Set Asymmetric Patterns.

  Local Definition is_leaf`(w : wavltree k g lg rg c) : bool :=
    match w with
    | Node _ _ _ _ _ _ _ _ (Missing _ _ _ _) _ _ (Missing _ _ _ _) _ _ => true
    | _ => false
    end.

  Local Ltac destruct_match := idtac;
    match goal with |- context[match ?X with _ => _ end] => destruct X end.

  Local Lemma leaf_rule_works`(w : wavltree k g lg rg c) : k = #0 <-> is_leaf w = true.
  Proof.
    unfold is_leaf.
    repeat destruct_match.
    boom.
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
    - eapply Node. reflexivity + eassumption.
    - eapply Missing. reflexivity.
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
Ltac use w := idtac; force refine w by boom.
Ltac use_regap w := idtac; force refine (setgap w _) by boom.
Ltac use_node := idtac;
  lazymatch goal with
    w: wavltree _ _ _ _ ?C |- wavltree _ _ _ _ ?C => use w + use_regap w
  end.
Ltac finish := idtac;
  match goal with
  | |- Esorted _ => ss
  | _ => boom
  end.

Section Insert_Rotations.

  Definition irot1`(lw : wavltree k #false llg lrg lc)(x : A)`(rw : wavltree (k - #2) #true rlg rrg rc)
    : llg = Enegb lrg -> Esorted(lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc).
  Proof.
    (* lw is higher than rw (k > k-2), so it makes sense to examine lw first *)
    ?? lw.
    - (* The right child of lw, rw0, needs to be combined somehow with rw.  rw0
         might be at the same height or 1 above rw, so that needs to be
         determined first.  But, if we first examine rw0 before examining its
         gap, we can eliminate the case when it is missing *)
      ?? (right_child lw).
      + (* rw0 is not missing, so examine its gap now *)
        ?? (gap (right_child lw)).
        * (* rw0 has a gap, so it is at k-2, the same as rw, which means the two
             can be combined easily with the result not havng a gap, so still
             fitting under k, rooted where lw already is *)
          rootify (datum lw). start_node.
          -- exact (left_child lw).
          -- rootify x. start_node.
             ++ use_regap (right_child lw).
             ++ use_regap rw.
             ++ finish.
             ++ finish.
          -- finish.
          -- finish.
        * (* rw0 has no gap, so we have to split it up with its left child lw1
             pairing with lw0, the regapped left child of lw, and its right
             child rw1 pairing with regapped rw, with the new root where rw0
             is *)
          rootify (datum (right_child lw)). start_node.
          -- start_node.
             ++ use_regap (left_child lw).
             ++ use (left_child (right_child lw)).
             ++ finish.
             ++ finish.
          -- start_node.
             ++ use (right_child (right_child lw)).
             ++ use_regap rw.
             ++ finish.
             ++ finish.
          -- finish.
          -- finish.
      + (* rw0 is missing - note that its sequence is now [] *)
        assert (k = #1) as -> by boom. rsimp.
        (* note that his implies rw is missing as well, because its height is -1 *)
        apply missing_contents in rw as ->.
        rootify (datum lw). start_node.
        * use (left_child lw).
        * start_node.
          -- missing.
          -- missing.
          -- finish.
          -- finish.
        * finish.
        * finish.
    - (* lw is missing, but that's not possible because rw is lower, so there is
         a contradiction *)
      boom.
  Qed.

  Definition irot2`(lw : wavltree (k - #2) #true llg lrg lc)(x : A)`(rw : wavltree k #false rlg rrg rc)
    : Enegb rlg = rrg -> Esorted(lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc).
  Proof.
    ?? rw.
    - ?? (left_child rw).
      + ?? (gap (left_child rw)).
        * rootify (datum rw). start_node.
          -- start_node.
             ++ use_node. (*use_regap lw.*)
             ++ use_node. (*use_regap (left_child rw).*)
             ++ finish.
             ++ finish.
          -- use_node. (*use (right_child rw).*)
          -- finish.
          -- finish.
        * rootify (datum (left_child rw)). start_node.
          -- start_node.
             ++ use_node. (*use_regap lw.*)
             ++ use_node. (*use (left_child (left_child rw)).*)
             ++ finish.
             ++ finish.
          -- start_node.
             ++ use_node. (*use (right_child (left_child rw)).*)
             ++ use_node. (*use_regap (right_child rw).*)
             ++ finish.
             ++ finish.
          -- finish.
          -- finish.
      + assert (k = #1) as -> by boom. rsimp. apply missing_contents in lw as ->.
        rootify (datum rw). start_node.
        * start_node.
          -- missing.
          -- missing.
          -- finish.
          -- finish.
        * use_node. (*use (right_child rw).*)
        * finish.
        * finish.
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
    allhyps_td f.

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

  Ltac tree_with x := idtac;
    match goal with
      H:wavltree _ _ _ _ ?C |- _ =>
      lazymatch C with context[x] => H end
    end.

  Notation "'tree_with' x" := ltac:(just tree_with x)
                                    (at level 199, no associativity, only parsing).

  Fixpoint insert(x : A)`(w : wavltree k g lg rg c) : insertResult x k g lg rg c.
  Proof.
    ?? w.
    - ?? (x =<> (datum w)).
      + eapply FoundByInsert. reflexivity.
      + ?? (insert x) on (left_child w).
        * ?? (pick insertedHow).
          -- assoc 0. eapply Inserted.
             ++ reflexivity.
             ++ rootify (datum w). start_node.
               ** use_node. (*use (tree_with x).*)
                ** use_node. (*use (right_child w).*)
                ** finish.
                ** finish.
             ++ eapply ISameK. boom.
          -- ?? (isMissing (right_child w)).
             ++ assoc 0. eapply Inserted.
                ** reflexivity.
                ** rootify (datum w). start_node.
                   --- use_node. (*use (tree_with x).*)
                   --- missing.
                   --- finish.
                   --- finish.
                ** eapply IHigherK. boom.
             ++ assoc 0. eapply Inserted.
                ** reflexivity.
                ** rootify (datum w). start_node.
                   --- use_node. (*use (tree_with x).*)
                   --- use_node. (*use (right_child w).*)
                   --- finish.
                   --- finish.
                ** eapply ISameK. boom.
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ assoc 0. eapply Inserted.
                ** reflexivity.
                ** rootify (datum w). start_node.
                   --- use_node. (*use (tree_with x).*)
                   --- use_node. (*use (right_child w).*)
                   --- finish.
                   --- finish.
                ** eapply ISameK. boom.
             ++ ?? (isgap (right_child w) false).
                ** assoc 0. eapply Inserted.
                   --- reflexivity.
                   --- rootify (datum w). start_node.
                       +++ use_node. (*use (tree_with x).*)
                       +++ use_node. (*use_regap (right_child w).*)
                       +++ finish.
                       +++ finish.
                   --- eapply IHigherK. boom.
                ** assoc 0. eapply Inserted.
                   --- reflexivity.
                   --- rootify (datum w). eapply irot1.
                       +++ use_node. (*use (tree_with x).*)
                       +++ use_node. (*use (right_child w).*)
                       +++ finish.
                       +++ finish.
                   --- eapply ISameK. boom.
        * rootify x. eapply FoundByInsert. reflexivity.
      + ?? (insert x) on (right_child w).
        * ?? (pick insertedHow).
          -- assoc 2. eapply Inserted.
             ++ reflexivity.
             ++ rootify (datum w). start_node.
                ** use_node. (*use (left_child w).*)
                ** use_node. (*use (tree_with x).*)
                ** finish.
                ** finish.
             ++ eapply ISameK. boom.
          -- ?? (isMissing (left_child w)).
             ++ assoc 2. eapply Inserted.
                ** reflexivity.
                ** rootify (datum w). start_node.
                   --- missing.
                   --- use_node. (*use (tree_with x).*)
                   --- finish.
                   --- finish.
                ** eapply IHigherK. boom.
             ++ assoc 2. eapply Inserted.
                ** reflexivity.
                ** rootify (datum w). start_node.
                   --- use_node. (*use (left_child w).*)
                   --- use_node. (*use (tree_with x).*)
                   --- finish.
                   --- finish.
                ** eapply ISameK. boom.
          -- unerase_gaps. ?? (gap (right_child w)).
             ++ assoc 2. eapply Inserted.
                ** reflexivity.
                ** rootify (datum w). start_node.
                   --- use_node. (*use (left_child w).*)
                   --- use_node. (*use (tree_with x).*)
                   --- finish.
                   --- finish.
                ** eapply ISameK. boom.
             ++ ?? (isgap (left_child w) false).
                ** assoc 2. eapply Inserted.
                   --- reflexivity.
                   --- rootify (datum w). start_node. all: [>use_node|use_node|..].
                    (* +++ use_regap (left_child w).
                       +++ use (tree_with x). *)
                       +++ finish.
                       +++ finish.
                   --- eapply IHigherK. boom.
                ** assoc 2. eapply Inserted.
                   --- reflexivity.
                   --- rootify (datum w). eapply irot2.
                       +++ use_node. (*use (left_child w).*)
                       +++ use_node. (*use (tree_with x).*)
                       +++ finish.
                       +++ finish.
                   --- eapply ISameK.  boom.
        * rootify x. eapply FoundByInsert. reflexivity.
    - eapply Inserted.
      + eapply nilnilnil.
      + start_node.
        * missing.
        * missing.
        * finish.
        * finish.
      + eapply IWasMissing. boom.
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
        * eapply TLlowered.
          -- reflexivity.
          -- reflexivity.
          -- start_node.
             ++ use_node. (*use_regap (left_child w).*)
             ++ use_node. (*use_regap (right_child w).*)
             ++ finish.
             ++ finish.
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
        * eapply Delout.
          -- apply DSameK.
             ++ reflexivity.
             ++ reflexivity.
          -- rootify (datum rw). start_node.
             ++ start_node.
                ** use_node. (*use lw.*)
                ** use_node. (*use (left_child rw).*)
                ** finish.
                ** finish.
             ++ use_node. (*use_regap (right_child rw).*)
             ++ finish.
             ++ finish.
        * eapply Delout.
          -- apply DSameK.
             ++ reflexivity.
             ++ reflexivity.
          -- rootify (datum (left_child rw)). start_node.
             ++ start_node. 1-2:use_node.
             (* ** use_node. (*use_regap lw.*)
                ** use_node. (*use (left_child (left_child rw)).*)*)
                ** finish.
                ** finish.
             ++ start_node.
                ** use_node. (*use (right_child (left_child rw)).*)
                ** use_node. (*use_regap (right_child rw).*)
                ** finish.
                ** finish.
             ++ finish.
             ++ finish.
      + assert (k = #2) as -> by boom. rsimp. apply missing_contents in lw as ->.
        eapply Delout.
        * apply DSameK.
          -- reflexivity.
          -- reflexivity.
        * rootify (datum rw). start_node.
          -- start_node.
             ++ missing.
             ++ missing.
             ++ finish.
             ++ finish.
          -- use_node. (*use_regap (right_child rw).*)
          -- finish.
          -- finish.
    - boom.
  Qed.

  Definition drot2`(lw : wavltree (k - #1) #false llg lrg lc)(x : A)`(rw : wavltree (k - #3) #true rlg rrg rc)
    : llg = #false \/ lrg = #false -> Esorted(lc++[x]++rc) -> forall g, delpair k #g (lc++[x]++rc).
  Proof.
    ?? lw.
    - ?? (right_child lw).
      + ?? (isgap (left_child lw) false).
        * eapply Delout.
          -- apply DSameK.
             ++ reflexivity.
             ++ reflexivity.
          -- rootify (datum lw). start_node.
             ++ use_node. (*use_regap (left_child lw).*)
             ++ rootify x. start_node.
                ** use_node. (*use (right_child lw).*)
                ** use_node. (*use rw.*)
                ** finish.
                ** finish.
             ++ finish.
             ++ finish.
        * eapply Delout.
          -- apply DSameK.
             ++ reflexivity.
             ++ reflexivity.
          -- rootify (datum (right_child lw)). start_node.
             ++ start_node. 1-2:use_node.
             (* ** use_node. (*use_regap (left_child lw).*)
                ** use_node. (*use (left_child (right_child lw)).*)*)
                ** finish.
                ** finish.
             ++ start_node.
                ** use_node. (*use (right_child (right_child lw)).*)
                ** use_node. (*use_regap rw.*)
                ** finish.
                ** finish.
             ++ finish.
             ++ finish.
      + assert (k = #2) as -> by boom. rsimp. apply missing_contents in rw as ->.
        eapply Delout.
        * apply DSameK.
          -- reflexivity.
          -- reflexivity.
        * rootify (datum lw). start_node.
          -- use_node. (*use_regap (left_child lw).*)
          -- start_node.
             ++ missing.
             ++ missing.
             ++ finish.
             ++ finish.
          -- finish.
          -- finish.
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
      + eapply MinDeleted.
        * rewrite Eapp_nil_l. reflexivity.
        * eapply Delout.
          -- apply DLowerK.
             ++ reflexivity.
             ++ reflexivity.
          -- use_node. (*use_regap rw.*)
      + ?? delmin on (left_child w).
        * boom.
        * ?? (pick delpair). ?? (pick deletedHow).
          -- eapply MinDeleted.
             ++ assoc 0. reflexivity.
             ++ eapply Delout.
                ** apply DSameK.
                   --- reflexivity.
                   --- reflexivity.
                ** start_node.
                   --- use_node. (*use ow.*)
                   --- use_node. (*use rw.*)
                   --- finish.
                   --- finish.
          -- ?? (isgap (right_child w) false).
             ++ ?? (isgap (left_child w) true).
                ** ?? (tryLowering (right_child w)).
                   --- eapply MinDeleted.
                       +++ assoc 0. reflexivity.
                       +++ eapply Delout.
                           *** apply DLowerK.
                               ---- reflexivity.
                               ---- reflexivity.
                           *** start_node.
                               ---- use_node. (*use ow.*)
                               ---- use_node. (*use ow0.*)
                               ---- finish.
                               ---- finish.
                   --- eapply MinDeleted.
                       +++ assoc 0. reflexivity.
                       +++ eapply drot1.
                           *** use_node. (*use ow.*)
                           *** use_node. (*use rw.*)
                           *** finish.
                           *** finish.
                ** eapply MinDeleted.
                   --- assoc 0. reflexivity.
                   --- eapply Delout.
                       +++ apply DSameK.
                           *** reflexivity.
                           *** reflexivity.
                       +++ start_node.
                           *** use_node. (*use ow.*)
                           *** use_node. (*use rw.*)
                           *** finish.
                           *** finish. 
             ++ unerase_gaps. eapply MinDeleted.
                ** assoc 0. reflexivity.
                ** eapply Delout.
                   --- apply DLowerK.
                       +++ reflexivity.
                       +++ reflexivity.
                   --- start_node.
                       +++ use_node. (*use_regap ow.*)
                       +++ use_node. (*use_regap rw.*)
                       +++ finish.
                       +++ finish.
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
      + eapply MaxDeleted.
        * rewrite Eapp_nil_r. reflexivity.
        * eapply Delout.
          -- apply DLowerK.
             ++ reflexivity.
             ++ reflexivity.
          -- use_node. (*use_regap lw.*)
      + ?? delmax on (right_child w).
        * boom.
        * ?? (pick delpair). ?? (pick deletedHow).
          -- eapply MaxDeleted.
             ++ assoc 2. reflexivity.
             ++ eapply Delout.
                ** apply DSameK.
                   --- reflexivity.
                   --- reflexivity.
                ** start_node.
                   --- use_node. (*use lw.*)
                   --- use_node. (*use ow.*)
                   --- finish.
                   --- finish.
        -- ?? (isgap (left_child w) false).
           ++  ?? (isgap (right_child w) true).
               ** ?? (tryLowering (left_child w)).
                  --- eapply MaxDeleted.
                      +++ assoc 2. reflexivity.
                      +++ eapply Delout.
                          *** apply DLowerK.
                              ---- reflexivity.
                              ---- reflexivity.
                          *** start_node.
                              ---- use_node. (*use ow0.*)
                              ---- use_node. (*use ow.*)
                              ---- finish.
                              ---- finish.
                  --- eapply MaxDeleted.
                      +++ assoc 2. reflexivity.
                      +++ eapply drot2.
                          *** use_node. (*use lw.*)
                          *** use_node. (*use ow.*)
                          *** finish.
                          *** finish.
               ** eapply MaxDeleted.
                  --- assoc 2. reflexivity.
                  --- eapply Delout.
                      +++ apply DSameK.
                          *** reflexivity.
                          *** reflexivity.
                      +++ start_node.
                          *** use_node. (*use lw.*)
                          *** use_node. (*use ow.*)
                          *** finish.
                          *** finish.
           ++ unerase_gaps. eapply MaxDeleted.
              ** assoc 2. reflexivity.
              ** eapply Delout.
                 --- apply DLowerK.
                     +++ reflexivity.
                     +++ reflexivity.
                 --- start_node.
                     +++ use_node. (*use_regap lw.*)
                     +++ use_node. (*use_regap ow.*)
                     +++ finish.
                     +++ finish.
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
        * eapply Deleted.
          -- reflexivity.
          -- eapply Delout.
             ++ apply DLowerK.
                ** reflexivity.
                ** reflexivity.
             ++ rewrite Eapp_nil_l. use_node. (*use_regap rw.*)
        * ?? (isMissing (right_child w)).
          -- eapply Deleted.
             ++ reflexivity.
             ++ eapply Delout.
                ** apply DLowerK.
                   --- reflexivity.
                   --- reflexivity.
                ** rewrite Eapp_nil_r. use_node. (*use_regap lw.*)
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ ?? (delmin (right_child w)).
                ** boom.
                ** ?? (pick delpair). ?? (pick deletedHow).
                   --- eapply Deleted.
                       +++ reflexivity.
                       +++ eapply Delout.
                           *** apply DSameK.
                               ---- reflexivity.
                               ---- reflexivity.
                           *** start_node.
                               ---- use_node. (*use lw.*)
                               ---- use_node. (*use ow.*)
                               ---- finish.
                               ---- finish.
                   --- eapply Deleted.
                       +++ reflexivity.
                       +++ eapply Delout.
                           *** apply DLowerK.
                               ---- reflexivity.
                               ---- reflexivity.
                           *** start_node.
                               ---- use_node. (*use_regap lw.*)
                               ---- use_node. (*use_regap ow.*)
                               ---- finish.
                               ---- finish.
             ++ ?? (delmax (left_child w)).
                ** boom.
                ** ?? (pick delpair). ?? (pick deletedHow).
                   --- eapply Deleted.
                       +++ reflexivity.
                       +++ eapply Delout.
                           *** apply DSameK.
                               ---- reflexivity.
                               ---- reflexivity.
                           *** assoc 0. start_node.
                               ---- use_node. (*use ow.*)
                               ---- use_node. (*use rw.*)
                               ---- finish.
                               ---- finish.
                   --- eapply Deleted.
                       +++ reflexivity.
                       +++ eapply Delout.
                           *** apply DSameK.
                               ---- reflexivity.
                               ---- reflexivity.
                           *** assoc 0. start_node.
                               ---- use_node. (*use ow.*)
                               ---- use_node. (*use rw.*)
                               ---- finish.
                               ---- finish.
      + ?? (delete x) on (left_child w).
        * ?? (pick delpair). ?? (pick deletedHow).
          -- eapply Deleted.
             ++ rootify x. reflexivity.
             ++ eapply Delout.
                ** apply DSameK.
                   --- reflexivity.
                   --- reflexivity.
                ** rootify d. start_node.
                   --- use_node. (*use ow.*)
                   --- use_node. (*use rw.*)
                   --- finish.
                   --- finish.
          -- unerase_gaps. ?? (gap (left_child w)).
             ++ unerase_gaps. ?? (gap (right_child w)).
                ** eapply Deleted.
                   --- rootify x. reflexivity.
                   --- eapply Delout.
                       +++ apply DLowerK.
                           *** reflexivity.
                           *** reflexivity.
                       +++ rootify d. start_node.
                           *** use_node. (*use ow.*)
                           *** use_node. (*use_regap rw.*)
                           *** finish.
                           *** finish.
                ** ?? (tryLowering (right_child w)).
                   --- eapply Deleted.
                       +++ rootify x. reflexivity.
                       +++ eapply Delout.
                           *** apply DLowerK.
                               ---- reflexivity.
                               ---- reflexivity.
                           *** rootify d. start_node.
                               ---- use_node. (*use ow.*)
                               ---- use_node. (*use ow0.*)
                               ---- finish.
                               ---- finish.
                   --- eapply Deleted.
                       +++ rootify x. reflexivity.
                       +++ rootify d. eapply drot1.
                           *** use_node. (*use ow.*)
                           *** use_node. (*use rw.*)
                           *** finish.
                           *** finish.
             ++ ?? (isMissing (right_child w)).
                ** eapply Deleted.
                   --- rootify x. reflexivity.
                   --- rootify d. eapply Delout.
                       +++ apply DLowerK.
                           *** reflexivity.
                           *** reflexivity.
                       +++ start_node.
                           *** use_node. (*use_regap ow.*)
                           *** missing.
                           *** finish.
                           *** finish.
                ** eapply Deleted.
                   --- rootify x. reflexivity.
                   --- eapply Delout.
                       +++ apply DSameK.
                           *** reflexivity.
                           *** reflexivity.
                       +++ rootify d. start_node.
                           *** use_node. (*use ow.*)
                           *** use_node. (*use rw.*)
                           *** finish.
                           *** finish.
        * eapply DNotFound. ss.
      + ?? (delete x) on (right_child w).
        * ?? (pick delpair). ?? (pick deletedHow).
          -- eapply Deleted.
             ++ rootify x. reflexivity.
             ++ rootify d. eapply Delout.
                ** apply DSameK.
                   --- reflexivity.
                   --- reflexivity.
                ** start_node.
                   --- use_node. (*use lw.*)
                   --- use_node. (*use ow.*)
                   --- finish.
                   --- finish.
          -- unerase_gaps. ?? (gap (right_child w)).
             ++ unerase_gaps. ?? (gap (left_child w)).
                ** eapply Deleted.
                   --- rootify x. reflexivity.
                   --- rootify d. eapply Delout.
                       +++ apply DLowerK.
                           *** reflexivity.
                           *** reflexivity.
                       +++ start_node.
                           *** use_node. (*use_regap lw.*)
                           *** use_node. (*use ow.*)
                           *** finish.
                           *** finish.
                ** ?? (tryLowering (left_child w)).
                   --- eapply Deleted.
                       +++ rootify x. reflexivity.
                       +++ rootify d. eapply Delout.
                           *** apply DLowerK.
                               ---- reflexivity.
                               ---- reflexivity.
                           *** start_node.
                               ---- use_node. (*use ow0.*)
                               ---- use_node. (*use ow.*)
                               ---- finish.
                               ---- finish.
                   --- eapply Deleted.
                       +++ rootify x. reflexivity.
                       +++ rootify d. eapply drot2.
                           *** use_node. (*use lw.*)
                           *** use_node. (*use ow.*)
                           *** finish.
                           *** finish.
             ++ ?? (isMissing (left_child w)).
                ** eapply Deleted.
                   --- rootify x. reflexivity.
                   --- rootify d. eapply Delout.
                       +++ apply DLowerK.
                           *** reflexivity.
                           *** reflexivity.
                       +++ start_node.
                           *** missing.
                           *** use_node. (*use_regap ow.*)
                           *** finish.
                           *** finish.
                ** eapply Deleted.
                   --- rootify x. reflexivity.
                   --- rootify d. eapply Delout.
                       +++ apply DSameK.
                           *** reflexivity.
                           *** reflexivity.
                       +++ start_node.
                           *** use_node. (*use lw.*)
                           *** use_node. (*use ow.*)
                           *** finish.
                           *** finish.
        * eapply DNotFound. ss.
    - eapply DNotFound. ss.
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

Extraction "wavl_noauto.ml" find insert delete.

(* Local Variables: *)
(* company-coq-local-symbols: (("++" . ?⧺) ("Esorted" . ?⊿) ("#" . ?◻) ("wavltree" . ?🎄) ("[]" . ?∅) ("^" . ?⋄) ("^#" . ?⟎) ("Enegb" . ?¬) ("true" . ?Ṫ) ("false" . ?Ḟ) ("EL" . ?Ḷ) ("EB" . ?Ḅ) ("EZ" . ?Ẓ)) *)
(* End: *)
