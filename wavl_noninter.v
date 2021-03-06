
(*** Weak AVL Trees ***)

(*+ 
See "Rank-Balanced Trees" by Haeupler, Sen, Tarjan
[http://www.cs.princeton.edu/~sssix/papers/rb-trees-talg.pdf].
*)

(* A non-interactive version of wavl.v, with all functions defined using ":=".
Note that the leaves of all but the most trivial functions are still filled in
using proof search. *)
Set Ltac Profiling.
Require Import elist.
Require Import ezbool.
Require Import utils.
Require Import hypiter.

Generalizable All Variables.
Set Implicit Arguments.

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
| Node{g : bool}(d : A)
      {geq: #g = pg}
      `{ceq: c = lc++[d]++rc}
      `(lw : wavltree (k - #1 - ^lg) lg llg lrg lc)
      `(rw : wavltree (k - #1 - ^rg) rg rlg rrg rc)
      {leaf_rule: k = #1 -> lg = #false \/ rg = #false}
      {sc: Esorted c}
| Missing{ceq: c = []}{keq: k = - #1}{lgeq: lg = #false}{rgeq: rg = #false}.

Arguments Missing {_ _ _ _ _ _ _ _ _}.

(**********************************************************************)

Notation "!" := ltac:(bang) (only parsing).

Section Lemmas.

  Definition wavl_min_rank`(w : wavltree k g lg rg c) : k >= - #1 :=
    wavltree_ind (fun k _ _ _ _ _ => k >= - #1) ! ! w.

  Definition wavl_node_min_rank`(w : wavltree k g lg rg c) : c <> [] -> k >= #0 :=
    match w with
    | Node _ lw _ =>
      let _ := wavl_min_rank lw in !
    | Missing => !
    end.

  Definition wavl_node_nonempty`(w : wavltree k g lg rg c) : k >= #0 -> c <> [] :=
    if w then ! else !.

  Definition missing_contents`(w : wavltree (- #1) g lg rg c) : c = [] :=
    let _ := (wavl_node_min_rank w) in
    if w then ! else !.

  Definition missing_rank`(w : wavltree k g lg rg []) : k = - #1 :=
    if w then ltac:(fnenil) else ltac:(tauto).

  Definition wavl_is_sorted`(w : wavltree k g lg rg c) : Esorted c :=
    if w then ltac:(assumption) else ltac:(subst; repeat econstructor).

End Lemmas.

Ltac bang_setup_tactic ::=
  let f H :=
      (lazymatch type of H with
       | wavltree _ _ _ _ _ =>
         first [apply missing_rank in H
               |apply wavl_node_min_rank in H; [|assumption||fnenil]
               |apply wavl_min_rank in H]
       | _ => idtac
       end) in
  allhyps_td f.

Ltac ss_setup_tactic :=
  let f H := (try apply wavl_is_sorted in H) in
  allhyps_td f.

Ltac ss := ss_setup_tactic; unerase; solve[solve_sorted].

(**********************************************************************)

Section Check_Leaf_Rule.
  
  Local Definition is_leaf`(w : wavltree k g lg rg c) : bool :=
    match w with
    | Node _ Missing Missing => true
    | _ => false
    end.

  Ltac destruct_match :=
    match goal with |- context[match ?X with _ => _ end] => destruct X end.

  Local Lemma leaf_rule_works`(w : wavltree k g lg rg c) : k = #0 <-> is_leaf w = true.
  Proof.
    unfold is_leaf.
    repeat destruct_match.
    all: boom.
  Qed.

End Check_Leaf_Rule.

(**********************************************************************)

(*notations to make these patterns short:*)
Notation eqcase := (CompEqT _ _ _) (only parsing).
Notation ltcase := (CompLtT _ _ _) (only parsing).
Notation gtcast := (CompGtT _ _ _) (only parsing).

Section Find.

  Inductive findResult(x : A)(c : EL) : Set :=
  | Found`(_: c = lc++[x]++rc)
  | NotFound(_: ENotIn x c).

  Ltac solve_find :=
    dintros;
    reassoc;
    ((eapply Found; reflexivity) || (eapply NotFound; ss)).

  Notation "!!" := ltac:(solve_find) (only parsing).

  Fixpoint find(x : A)`(w : wavltree k g lg rg c) : findResult x c :=
    match w with
    | Node d lw rw =>
      match x =<> d with
      | eqcase => !!
      | ltcase => if find x lw then !! else !!
      | gtcase => if find x rw then !! else !!
      end
    | Missing => !!
    end.

End Find.

Section SetGap.

  Notation "!!" := ltac:(econstructor; subst; try reflexivity; eassumption) (only parsing).

  Definition setgap`(w : wavltree k ig lg rg c)(og : bool) : wavltree k #og lg rg c :=
    if w then !! else !!.

End SetGap.

Section GetGap.

  Notation "!!" := ltac:(unshelve eexists; [exact false + eassumption | boom]) (only parsing).

  Definition getgap`(w : wavltree k g lg rg c) : {g' | c <> [] -> #g' = g} :=
    if w then !! else !!.

End GetGap.

Ltac unerase_var v :=
  lazymatch goal with
  | _ : # ?x = v |- _ => exact x
  | _ : v = # ?x |- _ => exact x
  end.

Notation "$ x" := ltac:(unerase_var x) (at level 10, only parsing).
  
Section IsGap.

  Notation "!!" := ltac:(constructor;boom) (only parsing).

  Notation "x ?= y" := (Bool.bool_dec x y) (only parsing).

  Definition isgap`(w : wavltree k g lg rg c)(g' : bool) : {k >= #0 /\ #g' = g} + {k = - #1 \/ #g' <> g} :=
    if w then (if g' ?= $ g then !! else !!) else !!.

End IsGap.

Notation "% w" := (isgap w true) (at level 20, only parsing).
Notation "~% w" := (isgap w false) (at level 20, only parsing).

Section IsMissing.

  Notation "!!" := ltac:(constructor;bang) (only parsing).

  Definition isMissing`(w : wavltree k g lg rg c) : {c = [] /\ k = - #1} + {c <> [] /\ k >= #0} :=
    if w then !! else !!.

End IsMissing.

Notation "~ w" := (isMissing w) (only parsing).

Ltac wavl_missing :=
  eapply Missing; [reflexivity|boom..].

Ltac wavl_assumption :=
  multimatch goal with W:wavltree _ _ _ _ ?C |- wavltree _ _ _ _ ?C' =>
    replace C' with C by (rewrite ?Eapp_assoc; reflexivity);
    (force exact W + force refine (setgap W _))
  end;[boom..].

Ltac solve_wavl :=
  dintros;
  (wavl_missing + wavl_assumption + wavl_construction)
with wavl_construction :=
  reassoc;
  eapply Node;
  [reflexivity
  |reflexivity
  |solve_wavl
  |solve_wavl
  |boom
  |ss].

Section Insert_Rotations.

  Notation "!!" := ltac:(solve_wavl) (only parsing).
  Notation "* b" := (Bool.Sumbool.sumbool_of_bool ($ b)) (at level 10, only parsing).
  
  Definition irot1`(lw : wavltree k #false llg lrg lc)(x : A)`(rw : wavltree (k - #2) #true rlg rrg rc)
    : llg = Enegb lrg -> Esorted (lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc) :=
    match lw with
    | Node _ llw lrw =>
      if lrw then (if *lrg then !! else !!) else !!
    | Missing => !
    end.
  
  Definition irot2`(lw : wavltree (k - #2) #true llg lrg lc)(x : A)`(rw : wavltree k #false rlg rrg rc)
    : Enegb rlg = rrg -> Esorted (lc++[x]++rc) -> forall g, wavltree k #g #false #false (lc++[x]++rc) :=
    match rw with
    | Node _ rlw rrw =>
      if rlw then (if *rlg then !! else !!) else !!
    | Missing => !
    end.

End Insert_Rotations.

Ltac use_rotations r1 r2 :=
  dintros;
  reassoc;
  (eapply r1 + eapply r2);
  [wavl_assumption
  |wavl_assumption
  |boom
  |ss].

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
                |specialize (X (wavl_node_nonempty H ltac:(bang)))];
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
            `(ih: insertedHow k ok g og olg org)
  | FoundByInsert`(_: c = lc++[x]++rc).

  Notation subtree's_k_unchanged :=
    (@Inserted _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@ISameK _ _ _ _ _ _ _ _)) (only parsing).
  Notation subtree_was_missing :=
    (@Inserted _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@IWasMissing _ _ _ _ _ _ _ _ _)) (only parsing).
  Notation subtree's_k_increased :=
    (@Inserted _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@IHigherK _ _ _ _ _ _ _ _ _ _)) (only parsing).
  Notation found_not_inserted :=
    (@FoundByInsert _ _ _ _ _ _ _ _ _) (only parsing).

  Ltac solve_wavl2 := use_rotations irot1 irot2 + solve_wavl.

  Definition nilnilnil : [] = [] ++ [] :> EL :=
    eq_ind_r (fun e : EL => [] = e) eq_refl (Eapp_nil_l []).

  Ltac solve_insert :=
    dintros;
    reassoc;
    ((eapply FoundByInsert; reflexivity) +
     (eapply Inserted;
      [reflexivity || eapply nilnilnil
      |solve_wavl2
      |econstructor;[boom..]
    ])).

  Notation "!!" := ltac:(solve_insert) (only parsing).

  Fixpoint insert(x : A)`(w : wavltree k g lg rg c) : insertResult x k g lg rg c :=
    match w with
    | Node d lw rw =>
      match x =<> d with
      | eqcase => !!
      | ltcase =>
        match insert x lw with
        | subtree's_k_unchanged => !!
        | subtree_was_missing => if ~rw then !! else !!
        | subtree's_k_increased => if %lw then !! else if ~%rw then !! else !!
        | found_not_inserted => !!
        end
      | gtcase =>
        match insert x rw with
        | subtree's_k_unchanged => !!
        | subtree_was_missing => if ~lw then !! else !!
        | subtree's_k_increased => if %rw then !! else if ~%lw then !! else !!
        | found_not_inserted => !!
        end
      end
    | Missing => !!
    end.
  
End Insert.

(**********************************************************************)

Section TryLowering.

  Inductive tryLoweringResult(k : EZ)(g lg rg : EB)(c : EL) : Set :=
  | TLlowered(_: lg = #true)(_: rg = #true)(ow: wavltree (k - #1) g #false #false c)
  | TLtooLow(_: lg = #false \/ rg = #false).

  Ltac solve_tl :=
    dintros;
    ((eapply TLlowered;
      [reflexivity
      |reflexivity
      |solve_wavl
     ])
     || (eapply TLtooLow; boom)).

  Notation "!!" := ltac:(solve_tl) (only parsing).

  Definition tryLowering`(w : wavltree k g lg rg c) : tryLoweringResult k g lg rg c :=
    match w with
    | Node d lw rw =>
      if %lw then (if %rw then !! else !!) else !!
    | Missing => !!
    end.

End TryLowering.

Notation "?↓ w" := (tryLowering w) (at level 10, only parsing).

Inductive deletedHow(ik ok : EZ)(ig og : EB) : Set :=
| DSameK(_: ok = ik)(_: og = ig)
| DLowerK(_:  ok = ik - #1)(_: og = #true).

Inductive delpair(k : EZ)(g : EB)(c : EL) : Set :=
| Delout`(dh : deletedHow k ok g og)`(ow : wavltree ok og olg org c).

Ltac solve_delpair :=
  dintros;
  eapply Delout;
  [constructor; [boom..]
  |solve_wavl
  ].

Section Delete_Rotations.

  Notation "!!" := ltac:(solve_delpair) (only parsing).

  Definition drot1
             `(lw : wavltree (k - #3) #true llg lrg lc)
             (x : A)
             `(rw : wavltree (k - #1) #false rlg rrg rc)
    : rlg = #false \/ rrg = #false -> Esorted (lc++[x]++rc) ->
      forall g, delpair k #g (lc++[x]++rc) :=
    match rw with
    | Node d rlw rrw => if rlw then (if ~%rrw then !! else !!) else !!
    | Missing => !
    end.

  Definition drot2
             `(lw : wavltree (k - #1) #false llg lrg lc)
             (x : A)
             `(rw : wavltree (k - #3) #true rlg rrg rc)
    : llg = #false \/ lrg = #false -> Esorted (lc++[x]++rc) ->
      forall g, delpair k #g (lc++[x]++rc) :=
    match lw with
    | Node d llw lrw => if lrw then (if ~%llw then !! else !!) else !!
    | Missing => !
    end.

End Delete_Rotations.

Ltac solve_delpair2 := use_rotations drot1 drot2 + solve_delpair.

Inductive delminResult(k : EZ)(g : EB)(c : EL) : Set :=
  MinDeleted(min : A)`(_: c = [min]++rc)(dp : delpair k g rc).

Notation delmin_subtree's_k_unchanged :=
  (@MinDeleted _ _ _ _ _ _ (@Delout _ _ _ _ _ (@DSameK _ _ _ _ _ _) _ _ _))
    (only parsing).

Notation delmin_subtree's_k_decreased :=
  (@MinDeleted _ _ _ _ _ _ (@Delout _ _ _ _ _ (@DLowerK _ _ _ _ _ _) _ _ _))
    (only parsing).

Section Delete_Minimum.

  Ltac solve_delmin :=
    dintros;
    reassoc;
    try rewrite Eapp_nil_l;
    eapply MinDeleted;
    [reflexivity|solve_delpair2].

  Notation "!!" := ltac:(solve_delmin) (only parsing).
  Notation "%!!" := ltac:(unerase_gaps; solve_delmin) (only parsing).

  Fixpoint delmin`(w : wavltree k g lg rg c) : k >= #0 -> delminResult k g c :=
    match w with
    | Node d lw rw =>
      if (isMissing lw) then !!
      else
        match (delmin lw !) with
        | delmin_subtree's_k_unchanged => !!
        | delmin_subtree's_k_decreased =>
          if ~%rw then (if %lw then (if ?↓rw then !! else !!) else !!) else %!!
        end
    | Missing => !
    end.

End Delete_Minimum.


Inductive delmaxResult(k : EZ)(g : EB)(c : EL) : Set :=
  MaxDeleted(max : A)`(_: c = lc++[max])(dp : delpair k g lc).

Notation delmax_subtree's_k_unchanged :=
  (@MaxDeleted _ _ _ _ _ _ (@Delout _ _ _ _ _ (@DSameK _ _ _ _ _ _) _ _ _))
    (only parsing).

Notation delmax_subtree's_k_decreased :=
  (@MaxDeleted _ _ _ _ _ _ (@Delout _ _ _ _ _ (@DLowerK _ _ _ _ _ _) _ _ _))
    (only parsing).

Section Delete_Maximum.

  Ltac solve_delmax :=
    dintros;
    reassoc;
    try rewrite Eapp_nil_r;
    eapply MaxDeleted;
    [reflexivity|solve_delpair2].

  Notation "!!" := ltac:(solve_delmax) (only parsing).
  Notation "%!!" := ltac:(unerase_gaps; solve_delmax) (only parsing).

  Fixpoint delmax`(w : wavltree k g lg rg c) : k >= #0 -> delmaxResult k g c :=
    match w with
    | Node d lw rw =>
      if (isMissing rw) then !!
      else
        match (delmax rw !) with
        | delmax_subtree's_k_unchanged => !!
        | delmax_subtree's_k_decreased =>
          if ~%lw then (if %rw then (if ?↓lw then !! else !!) else !!) else %!!
        end
    | Missing => !
    end.

End Delete_Maximum.

Section Delete.

  Inductive deleteResult(x : A)(k : EZ)(g : EB)(c : EL) : Set :=
  | Deleted`(_: c = lc++[x]++rc)(dp : delpair k g (lc++rc))
  | DNotFound(_: ENotIn x c).

  Notation deleted_subtree's_k_unchanged :=
    (@Deleted _ _ _ _ _ _ _ (@Delout _ _ _ _ _ (@DSameK _ _ _ _ _ _) _ _ _))
      (only parsing).
  Notation deleted_subtree's_k_decreased :=
    (@Deleted _ _ _ _ _ _ _ (@Delout _ _ _ _ _ (@DLowerK _ _ _ _ _ _) _ _ _))
      (only parsing).
  Notation delete_target_not_found :=
    (@DNotFound _ _ _ _ _) (only parsing).

  Ltac solve_delete :=
    dintros;
    reassoc;
    ((eapply Deleted;
      [reflexivity (* c = lc++[x]++rc *)
      |(rewrite Eapp_nil_r + rewrite Eapp_nil_l + idtac); solve_delpair2
      ])
     + (eapply DNotFound; ss)).

  Notation "!!" := ltac:(solve_delete) (only parsing).
  Notation "%!!" := ltac:(unerase_gaps; solve_delete) (only parsing).

  Fixpoint delete(x : A)`(w : wavltree k g lg rg c) : deleteResult x k g c :=
    match w with
    | Node d lw rw =>
      match x =<> d with
      | eqcase =>
        if (isMissing lw) then !!
        else if (isMissing rw) then !!
             else if %lw
                  then match (delmin rw !) with
                       | delmin_subtree's_k_unchanged => !!
                       | delmin_subtree's_k_decreased => %!!
                       end
                  else match (delmax lw !) with
                       | delmax_subtree's_k_unchanged => !!
                       | delmax_subtree's_k_decreased => !!
                       end
      | ltcase =>
        match (delete x lw) with
        | deleted_subtree's_k_unchanged => !!
        | deleted_subtree's_k_decreased =>
          if %lw then (if %rw then !! else if ?↓rw then !! else !!)
          else if ~rw then !! else !!
        | delete_target_not_found => !!
        end
      | gtcase =>
        match (delete x rw) with
        | deleted_subtree's_k_unchanged => !!
        | deleted_subtree's_k_decreased =>
          if %rw then (if %lw then !! else if ?↓lw then !! else !!)
          else if ~lw then !! else !!
        | delete_target_not_found => !!
        end
      end
    | Missing => !!
    end.

End Delete.
Show Ltac Profile CutOff 1.
Set Printing Width 120.

Require Import ExtrOcamlBasic.

Extract Inductive delpair => "( * )" [ "" ].
Extract Inductive delminResult => "( * )" [ "" ].
Extract Inductive delmaxResult => "( * )" [ "" ].

Extraction Inline negb.

Extract Inlined Constant Bool.bool_dec => "(=)".

Extraction Inline Bool.Sumbool.sumbool_of_bool.

Extraction "wavl_noninter.ml" find insert delete.
