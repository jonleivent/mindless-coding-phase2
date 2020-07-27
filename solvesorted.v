(**** 
Reflection procedure for sorted (=LocallySorted lt) solves goals of the form:
  forall (a b : A)(p q r : list A), 
  sorted(a::p++q++r) -> sorted(p++r++[b]) -> sorted(q++[b]) -> a<b ->
  sorted(p++q++r++[b]).
where A is an ordered class.  Also handles a ∉ l terms.
****)

Set Default Goal Selector "all".

From Coq Require Import Lists.List.
From mindless Require Import ordered.
Import ListNotations.
From Coq Require Export Sorting.Sorted.

Module Reified.
  
  Inductive List_formula :=
  | LF_nil : List_formula
  | LF_cons : nat -> List_formula -> List_formula
  | LF_list : nat -> List_formula
  | LF_app : List_formula -> List_formula -> List_formula.

  Inductive Sorted_formula :=
  | SF_lt : nat -> nat -> Sorted_formula (*a<b*)
  | SF_sorted : List_formula -> Sorted_formula
  | SF_notin : nat -> List_formula -> Sorted_formula
  | SF_and : Sorted_formula -> Sorted_formula -> Sorted_formula
  | SF_or : Sorted_formula -> Sorted_formula -> Sorted_formula
  | SF_imp : Sorted_formula -> Sorted_formula -> Sorted_formula
  | SF_skip : Prop -> Sorted_formula. (*unreified props*)
  
End Reified.

Module Notations.
  
  Notation sorted := (LocallySorted lt).

  Definition NotIn{A}(x : A)(l : list A) := ~In x l.

  Infix "<" := lt (at level 70) : list_scope.

  Infix "∈" := In (at level 55) : list_scope.

  Infix "∉" := NotIn (at level 55) : list_scope.
End Notations.
 
Module Reflection.
  Export Reified.
  
  Fixpoint flatten(lf : List_formula) {struct lf} : list nat :=
    match lf with
    | LF_nil => nil
    | LF_cons i lf' => i :: flatten lf'
    | LF_list i => [i]
    | LF_app lf1 lf2 => flatten lf1 ++ flatten lf2
    end.

  Definition Known := list (nat * nat).
  (*There are currently 2 knowns, referred to as kord (ordered knowns produced by sorted an < hyps) and knin (produced by NotIn hyps).  Both share some features, but kord knowns are tansitive through singletons.  Also note that the fst of each pair in knin knowns are always singletons.*)

  Definition add_known(i j:nat)(k:Known) : Known := (i,j)::k.

  Fixpoint add_knowns(i:nat)(k:Known)(js:list nat) : Known :=
    match js with
    | nil => k
    | j::js' => add_knowns i (add_known i j k) js'
    end.

  (*add_known of (i,0) in the i::nil case is a kludge, as 0 is always nil, to allow lone list atoms (sorted l) to be seen as sorted.  This is why we keep index 0 provably pinned to nil in aDenote and isA below*)
  Fixpoint forward_flat(cont:Known->bool)(js:list nat)(kord:Known) : bool :=
    match js with
    | nil => cont kord
    | i::nil => cont (add_known i 0 kord)
    | i::js => forward_flat cont js (add_knowns i kord js)
    end.

  Fixpoint forward(cont:Known->Known->bool)(hyp:Sorted_formula)(kord knin:Known) : bool :=
    let next cont hyp := forward cont hyp kord knin in
    match hyp with
    | SF_lt i j => cont (add_known i j kord) knin
    | SF_sorted lf => forward_flat (fun kord => cont kord knin) (flatten lf) kord
    | SF_notin i lf => cont kord (add_knowns i knin (flatten lf))
    | SF_and h1 h2 => next (forward cont h2) h1
    | SF_or h1 h2 => if next cont h1 then next cont h2 else false
    | _ => cont kord knin
    end.

  Fixpoint is_known (i j:nat)(k:Known) : bool :=
    match k with
    | nil => false
    | (x,y)::k' =>
      if Nat.eqb i x
      then if Nat.eqb j y then true
           else is_known i j k'
      else is_known i j k'
    end.

  (*check needed for sorted of a lone list atom i - only need to check if (i,j) is known for any j, no need to check (j,i) because forward_flat always adds (i,0) at the end*)
  Fixpoint is_kord1 (i:nat)(kord:Known) : bool :=
    match kord with
    | nil => false
    | (x,_)::kord => if Nat.eqb x i then true else is_kord1 i kord
    end.

  Section Backward.
    Variable Singles : list nat.

    Definition isSingleton a := existsb (Nat.eqb a) Singles.

    (*ito_inner and ito_outer are the inner and outer loops for is_trans_ord.  The continuation style (c param) makes the code lighter weight than using well_founded induction.  Both inner and outer loop over Singles, the list of all singletons, looking for chains of singletons related by < from src to dst.  Only singletons are involved because < is transitive with respect to singletons but not list atoms (because list atoms might evaluate to nil)*)
    Fixpoint ito_inner(c: nat -> bool)(kord:Known)(dst src : nat)(l:list nat) : bool :=
      let next := ito_inner c kord dst src in
      match l with
      | mid :: l =>
        if is_known src mid kord
        then if is_known mid dst kord then true
             else if c mid then true
                  else next l
        else next l
      | nil => false
      end.

    Fixpoint ito_outer(kord:Known)(l:list nat)(dst src:nat) : bool :=
      match l with
      | _::l => ito_inner (ito_outer kord l dst) kord dst src Singles
      | nil => false
      end.

    Definition is_trans_ord(i j:nat)(kord:Known) :=
      if is_known i j kord then true else ito_outer kord Singles j i.
    
    (*all_ord i k l := i is known to be <# every j in l
    Note that we could test to see if i must be nil first, to avoid all further checks, but this is rare, so we put it off until other checks fail *)
    Fixpoint all_ord(i:nat)(kord:Known)(l:list nat) : bool :=
      match l with
      | nil => if isSingleton i then true else is_kord1 i kord
      | j::l' =>
        if is_trans_ord i j kord
        then if isSingleton j then true else all_ord i kord l'
        else if is_trans_ord i i kord (*i is nil*) then true
             else if is_trans_ord j j kord (*j is nil*)
                  then if isSingleton j then true else all_ord i kord l'
                  else false
      end.
    
    Fixpoint backward_flat_ord(kord:Known)(l:list nat) :=
      match l with
      | nil => true
      | i::l => if all_ord i kord l then backward_flat_ord kord l else false
      end.

    (*i is not in l iff forall j in l:
      - i is known to not be in j
      - i < j
      - j < i
      - j is nil (j < j) *)
    Fixpoint backward_flat_nin(kord knin:Known)(i:nat)(l:list nat) :=
      let next := backward_flat_nin kord knin i in
      match l with
      | nil => true
      | j::l =>
        if is_known i j knin then next l
        else if is_trans_ord i j kord then next l
             else if is_trans_ord j i kord then next l
                  else if is_trans_ord j j kord then next l
                       else false
      end.
    
    (*true if there exists singleton i with i <# i including by transitivity, which is a contradiction because < is irreflexive.*)
    Fixpoint lt_self(kord : Known) : bool :=
      match kord with
      | nil => false
      | (i,j)::kord' => if isSingleton i then is_trans_ord i i kord else lt_self kord'
      end.

    (*true if there exists singleton i with NotIn i [..i..], which is a contradiction*)
    Fixpoint nin_self(knin : Known) : bool :=
      match knin with
      | nil => false
      | (i,j)::kmin =>
        if Nat.eqb i j then
          if isSingleton i then true
          else nin_self kmin
        else nin_self kmin
      end.

    Definition has_contra(kord knin: Known) : bool :=
      if nin_self knin then true else lt_self kord.

    (*Note that in backward we may end up calling has_contra more than once even if it is true, because backward does not separate out the top-level of conclusion from subformulae.  Every time backward hits SF_imp, the f2 part is a new sub conclusion that may need its own has_contra call (because it can have more knowns due to f1), so we cannot have just one top-level has_contra call.  This leads to some complex wiring - so the easiest thing to do is just test has_contra after each potential low-level conclusion *)
    Fixpoint backward(f:Sorted_formula)(kord knin:Known) : bool :=
      let next f := backward f kord knin in
      match f with
      | SF_lt i j =>
        if is_trans_ord i j kord then true else has_contra kord knin
      | SF_sorted lf =>
        if backward_flat_ord kord (flatten lf) then true else has_contra kord knin
      | SF_notin i lf =>
        if isSingleton i then (*because reflection doesn't know reifier isn't cheating*)
          if backward_flat_nin kord knin i (flatten lf) then true
          else has_contra kord knin
        else has_contra kord knin
      | SF_and f1 f2 =>
        if next f1 then next f2 else false
      | SF_or f1 f2 =>
        if next f1 then true else next f2
      | SF_imp f1 f2 => forward (backward f2) f1 kord knin
      | SF_skip _ => has_contra kord knin
      end.

  End Backward.
End Reflection.

Module Reflection_Proof.
  Import Reflection.
  Import Notations.

  Tactic Notation "deif" :=
    lazymatch goal with
    | |- context[match ?C with _ => _ end] => destruct (C)
    end.

  Tactic Notation "deif" "as" ident(E) :=
    lazymatch goal with
    | |- context[match ?C with _ => _ end] => destruct (C) eqn:E
    end.

  Tactic Notation "deif" hyp(H) :=
    lazymatch type of H with
    | context[match ?C with _ => _ end] => destruct (C)
    end.

  Tactic Notation "deif" hyp(H) "as" ident(E) :=
    lazymatch type of H with
    | context[match ?C with _ => _ end] => destruct (C) eqn:E
    end.

  Local Ltac recon := idtac + (constructor; recon).

  Local Ltac tea := subst; try (cbn in *;intuition (congruence + (recon; eassumption))).

  Local Ltac eappit := match goal with H:_ |- _ => eapply H; solve [tea | eappit] end.

  Definition nat_eq_dec(i j:nat) : {i=j}+{i<>j}.
  Proof.
    decide equality.
  Defined.

  Set Mangle Names.
  Set Mangle Names Prefix "α".

  Lemma ifeqtrue : forall (b:bool), (if b then true else false) = true <-> b = true.
  Proof with tea.
    intros []...
  Qed.

  Lemma ifeqtrue2 : forall (b1 b2:bool),
      (if b1 then true else b2) = true <-> b1 = true \/ b2 = true.
  Proof with tea.
    intros [] ? ... 
  Qed.

  Lemma ifeqtrue3: forall (b1 b2:bool),
      (if b1 then b2 else false) = true <-> b1 = true /\ b2 = true.
  Proof with tea.
    intros [] ? ...
  Qed.

  Lemma ifeqtrue4: forall (b1 b2:bool), (if b1 then b2 else b2) = true <-> b2 = true.
  Proof with tea.
    intros [] ? ...
  Qed.

  Lemma nat_eqb_eq: forall i j, Nat.eqb i j = true <-> i=j.
  Proof with tea.
    intro i. induction i. intros []. cbn...
    split. intro H.
    - f_equal. eappit.
    - injection H. eappit.
  Qed.

  Lemma nat_eqb_self: forall i, Nat.eqb i i = true.
  Proof with tea.
    intro i. induction i...
  Qed.

  Lemma neq_nat_eqb: forall i j, i<>j -> Nat.eqb i j = false.
  Proof with tea.
    intros i j H. destruct (Nat.eqb i j) eqn:E...
    apply nat_eqb_eq in E...
  Qed.

  Local Ltac dorws :=
    repeat first[rewrite ifeqtrue4 in *
                |rewrite ifeqtrue in *
                |rewrite ifeqtrue2 in *
                |rewrite ifeqtrue3 in *
                |rewrite nat_eqb_self in *
                |rewrite nat_eqb_eq in *
                |rewrite neq_nat_eqb in * by congruence].

  Section Reflect_Proof.
    Context {A : Set}.
    Context {ordA : Ordered A}.
    
    Inductive Atom := Aatom(_:A) | Latom(_:list A).

    Section With_Atomics.
      Variable atomics : list Atom.
      Hypothesis atomics0nil : nth 0 atomics (Latom nil) = (Latom nil).

      Definition aDenote i : list A :=
       match (nth i atomics (Latom nil)) with
       | Aatom a => [a]
       | Latom l => l
        end.
      
      Definition isA i : bool :=
        match (nth i atomics (Latom nil)) with
        | Aatom _ => true
        | Latom _ => false
        end.

      Fixpoint lfDenote(lf : List_formula) : list A :=
        match lf with
        | LF_nil => nil
        | LF_cons i lf' => aDenote i ++ lfDenote lf'
        | LF_list i => aDenote i
        | LF_app lf1 lf2 => lfDenote lf1 ++ lfDenote lf2
        end.

      Fixpoint fDenote(l: list nat) : list A :=
        match l with
        | nil => nil
        | i::l => aDenote i ++ fDenote l
        end.

      Notation "X '<#' Y" := (sorted (aDenote X ++ aDenote Y)) (at level 70) : list_scope.

      (*lemmas showing that flattening is correct*)
      
      Lemma flatten_app : forall l1 l2, fDenote (l1++l2) = fDenote l1 ++ fDenote l2.
      Proof with tea.
        intro l1. induction l1. intros... cbn. rewrite <-app_assoc...
      Qed.

      Lemma flatten_valid: forall lf, lfDenote lf = fDenote (flatten lf).
      Proof with tea.
        intro lf. induction lf. cbn...
        - apply app_nil_end.
        - rewrite flatten_app...
      Qed.

      (**)

      Definition nin i lf :=
        match (aDenote i) with
        | [a] => a ∉ (lfDenote lf)
        | _ => False
        end.

      (*flattened version of nin*)
      Definition ninf i l :=
        match (aDenote i) with
        | [a] => a ∉ (fDenote l)
        | _ => False
        end.

      Lemma ninf2nin : forall{i l}, ninf i (flatten l) <-> nin i l.
      Proof with tea.
        intros i l. split. intro H. hnf in *. rewrite flatten_valid in * ...
      Qed.

      Local Ltac denin :=
        let x:=fresh in
        lazymatch goal with
        | H: isA ?i = true |- _ =>
          unfold nin,ninf in *;
          unfold isA in H; cbn in *;
          set(x:=(aDenote i)) in *;
          unfold aDenote in x;
          destruct (nth _ atomics _);
          subst x;
          cbn in *
        end.

      Fixpoint sfDenote(sf : Sorted_formula) : Prop :=
        match sf with
        | SF_lt i j =>
          (*kludge needed here because proofs don't know i and j are always singletons*)
          match (aDenote i), (aDenote j) with
          | [a], [b] => a<b (*for convertibility, we cannot use i <# j*)
          | _, _ => i <# j (*should not occur, but needed for correctness*)
          end
        | SF_sorted lf => sorted (lfDenote lf)
        | SF_notin i lf => nin i lf
        | SF_and sf1 sf2 => sfDenote sf1 /\ sfDenote sf2
        | SF_or sf1 sf2 => sfDenote sf1 \/ sfDenote sf2
        | SF_imp sf1 sf2 => sfDenote sf1 -> sfDenote sf2
        | SF_skip p => p
        end.

      (*prevent sfDenote (SF_lt i j) from reducing to the < vs. <# kludge:*)
      Lemma sflt_norm: forall i j, sfDenote (SF_lt i j) <-> i <# j.
      Proof with tea.
        intros i j. split. intro H. cbn in *.
        do 2 destruct (aDenote _) as [|? []]... inversion H...
      Qed.

      (*lemmas about sorted - all are opaque*)

      Lemma sorted_left : forall {l1 l2}, sorted (l1++l2) -> sorted l1.
      Proof with tea.
        intro l1. induction l1 as [ |a l1 IHl1]... 
        intros l2 H. destruct l1... inversion H... constructor... eapply IHl1...
      Qed.

      Lemma sorted_right : forall {l1 l2}, sorted (l1++l2) -> sorted l2.
      Proof with tea.
        intro l1. induction l1 as [|a l1 IHl1].
        intros l2 H... destruct l1. inversion H... eapply IHl1...
      Qed.

      Lemma sorted_tail : forall {l a}, sorted (a::l) -> sorted l.
      Proof with tea.
        intros l a H. inversion H...
      Qed.

      Lemma sorted_combine : forall {l1 l2 a}, sorted(l1++[a]) -> sorted([a]++l2) -> sorted(l1++[a]++l2).
      Proof with tea.
        intro l1. induction l1 as [|a l1 IHl1]. intros l2 ? H1 H2...
        destruct l1. cbn in *. constructor... inversion H1... apply IHl1...
      Qed.

      Lemma sorted_overlap : forall {l1 l2 l3 a b},
          sorted(l1++a::l2) -> sorted(l2++b::l3) -> a<b -> sorted(l1++a::l2++b::l3).
      Proof with tea.
        intro l1. induction l1 as [|a l1 IHl1]. intros l2 l3 ? ? H H0 H1.
        - destruct l2... inversion H... 
        - destruct l1. cbn in *. inversion H. subst. constructor... eapply IHl1...
      Qed.

      Lemma sorted2lt : forall {l1 l2 a b}, sorted (a::l1++b::l2) -> a<b.
      Proof with tea.
        intro l1. induction l1 as [|a l1 IHl1]. intros ? ? ? H. inversion H... 
        transitivity a... eapply IHl1...
      Qed.

      Lemma sorted_delmid : forall {l1 l2 l3}, sorted (l1++l2++l3) -> sorted (l1++l3).
      Proof with tea.
        intro l1. induction l1 as [|a l1 IHl1]. intros l2 l3 H.
        - eapply sorted_right...
        - destruct l1.
          + destruct l3... constructor.
            * do 2 apply sorted_right in H...
            * apply sorted2lt in H...
          + inversion H... cbn. constructor... eapply IHl1...
      Qed.

      Lemma sorted_3way : forall {l1 l2 l3}, sorted(l1++l2) -> sorted(l2++l3) -> sorted(l1++l3) -> sorted(l1++l2++l3).
      Proof with tea.
        intros l1 [] [] H1 H2 H3. cbn in *. rewrite ?app_nil_r in *...
        eapply sorted_overlap...
        - eapply sorted_tail...
        - eapply sorted2lt...
      Qed.

      (*lemmas about NotIn*)

      Lemma NotInBoth: forall {l1 l2}{x:A}, x ∉ (l1++l2) <-> (x ∉ l1 /\ x ∉ l2).
      Proof with tea.
        intros l1 l2 x. split.
        - intro H1. split. intro H2. apply H1. apply in_or_app...
        - intros (H1 & H2) H3. apply in_app_or in H3...
      Qed.

      Lemma NotInl: forall {l x}, sorted (x::l) -> x ∉ l.
      Proof with tea.
        intro l. induction l as [|y l IHl]. intros x H. unfold NotIn...
        cbn. intros [H1|H1]. subst.
        - eapply irreflexivity. inversion H...
        - eapply IHl... change (x::y::l) with ([x]++[y]++l) in H.
          apply sorted_delmid in H...
      Qed.

      Lemma NotInr: forall {l x}, sorted (l++[x]) -> x ∉ l.
      Proof with tea.
        intro l. induction l as [|y l IHl]. intros x H. unfold NotIn...
        cbn. intros [H1|H1]. subst.
        - change ((x::l)++[x]) with ([x]++l++[x]) in H.
          apply sorted_delmid in H. eapply irreflexivity. inversion H...
        - cbn in H. apply sorted_tail in H. eapply IHl...
      Qed.

      (**)

      Fixpoint allOrdered(kord:Known) : Prop :=
        match kord with
        | nil => True
        | (i, j)::kord' => i <# j /\ allOrdered kord'
        end.

      Fixpoint allNotIn(knin:Known) : Prop :=
        match knin with
        | nil => True
        | (i, j)::knin' => nin i (LF_list j) /\ allNotIn knin'
        end.
      
      Lemma in_allOrdered: forall{kord i j}, allOrdered kord -> In (i, j) kord -> i <# j.
      Proof with tea.
        intro kord. induction kord as [|a kord IHk]. intros i j. cbn... 
        intros H [->|]... destruct a. apply IHk...
      Qed.

      Lemma sorted_single: forall{a}, isA a = true -> sorted (aDenote a).
      Proof with tea.
        intros a H. unfold isA in H. unfold aDenote. deif... deif...
      Qed.

      Lemma sorted_alone: forall{kord a},
          allOrdered kord -> is_kord1 a kord = true -> sorted (aDenote a).
      Proof with tea.
        intro kord. induction kord as [|[i j] kord IHk]. intros n H1 H2... cbn in *.
        dorws. destruct H1, H2. subst.
        - eapply sorted_left...
        - eappit.
      Qed.

      Lemma is_known_In: forall{k i j}, is_known i j k = true -> In (i,j) k.
      Proof with tea.
        intro k. induction k as [|[x y] k IHk]. intros i j H... cbn in H.
        destruct (nat_eq_dec i x). subst. dorws. 1:destruct H... right. eappit.
      Qed.

      Lemma known_ord: forall{kord i j}, is_known i j kord = true -> allOrdered kord -> i <# j.
      Proof with tea.
        intros. eapply in_allOrdered... eapply is_known_In...
      Qed.

      Lemma known_nin: forall{knin i j},
          is_known i j knin = true -> allNotIn knin -> nin i (LF_list j).
      Proof with tea.
        intro knin. induction knin as [|[x y] k IHk]. intros i j H1 []... cbn in H1.
        destruct (nat_eq_dec i x). subst. dorws... 1:destruct H1... eappit.
      Qed.

      Lemma ord_trans: forall {a b c},
          a <# b -> sorted(aDenote b ++ fDenote c) -> isA b = true -> sorted(aDenote a ++ fDenote c).
      Proof with tea.
        intros a b c H1 H2 H3. unfold isA in H3.
        set (xb := aDenote b) in *. unfold aDenote in xb. subst xb. 
        deif H3... eapply sorted_delmid... eapply sorted_combine...
      Qed.

      Lemma ord_trans1: forall {a b c}, a <# b -> b <# c -> isA b = true -> a <# c.
      Proof with tea.
        intros a b c H1 H2 H3.
        replace (aDenote c) with (fDenote [c]) in * by (apply app_nil_r).
        eapply ord_trans...
      Qed.

      Fixpoint is_sings(l:list nat) : Prop :=
        match l with
        | s::l => isA s = true /\ is_sings l
        | nil => True
        end.

      Lemma ito_inner_valid : forall{kord l c i j},
          (forall m, isA m = true -> i <# m -> c m = true -> i <# j) ->
          allOrdered kord -> is_sings l -> ito_inner c kord j i l = true -> i <# j.
      Proof with tea.
        intros kord l. induction l as [|m l IHl]. intros c i j H H1 H2 H3...
        destruct H2. cbn in H3. deif H3 as E1. 2:eapply IHl...
        apply known_ord in E1... dorws. destruct H3 as [|[]].
        - eapply ord_trans1... eapply known_ord...
        - eapply H...
        - eapply IHl...
      Qed.

      Fixpoint is_lsings(ll:list (list nat)) : Prop :=
        match ll with
        | l :: ll => is_sings l /\ is_lsings ll
        | nil => True
        end.

      Lemma ito_outer_valid : forall{kord l1 l2 i j},
          allOrdered kord -> is_sings l1 -> is_sings l2 ->
          ito_outer l1 kord l2 j i = true -> i <# j.
      Proof with tea.
        intros kord l1 l2. induction l2. intros i j H1 H2 H3 H4...
        eapply ito_inner_valid in H4... intros. eapply ord_trans1... eappit.
      Qed.

      Lemma ito_valid : forall{i j l kord},
          allOrdered kord -> is_sings l -> is_trans_ord l i j kord = true -> i <# j.
      Proof with tea.
        intros i j l kord H1 H2 H3. unfold is_trans_ord in H3. deif H3 as E. 
        - eapply known_ord...
        - eapply ito_outer_valid...
      Qed.

      Lemma ord_self_single : forall{i}, i <# i -> isA i = true -> False.
      Proof with tea.
        intros i H1 H2. unfold aDenote in H1. unfold isA in H2.
        deif H2... eapply irreflexivity. inversion H1...
      Qed.

      Lemma ord_self_nil : forall{i}, i <# i -> aDenote i = nil.
      Proof with tea.
        intros i H. destruct (aDenote i)... cbn in H. eelim irreflexivity. eapply sorted2lt...
      Qed.

      Lemma sing_sing: forall{i sl}, is_sings sl -> isSingleton sl i = true -> isA i = true.
      Proof with tea.
        intros i sl. induction sl as [|j sl IHsl]. cbn... intros [] H.
        destruct (nat_eq_dec i j). subst. dorws...
      Qed.

      Lemma sorted_push: forall{i kord sl l},
          allOrdered kord -> is_sings sl -> all_ord sl i kord l = true -> sorted (fDenote l) ->
          sorted (aDenote i ++ fDenote l).
      Proof with tea.
        intros i kord sl l H0 H1 H2 H3. induction l. cbn in H2.
        { rewrite app_nil_r. dorws. destruct H2.
          - eapply sorted_single... eapply sing_sing...
          - eapply sorted_alone... }
        cbn [fDenote] in *. apply sorted_right in H3 as H4. deif H2 as E1. dorws.
        { apply ito_valid in E1... eapply sorted_3way... destruct H2... eapply ord_trans...
          eapply sing_sing... }
        destruct H2 as [H2|[H2 []]]. eapply ito_valid in H2...
        - rewrite (ord_self_nil H2)...
        - eapply ord_self_single in H2... eapply sing_sing...
        - rewrite (ord_self_nil H2)...
      Qed.
      
      Lemma backward_flat_ord_valid: forall{kord sl l},
          is_sings sl -> allOrdered kord -> backward_flat_ord sl kord l = true ->
          sorted (fDenote l).
      Proof with tea.
        intros kord sl l H1 H2. induction l as [|a l IHl]. intro H3... cbn in H3.
        destruct l. dorws.
        - cbn in *. rewrite app_nil_r. dorws. destruct H3.
          + eapply sorted_single... eapply sing_sing...
          + eapply sorted_alone...
        - destruct H3. eapply sorted_push...
      Qed.

      Lemma backward_flat_nin_valid: forall{i kord knin sl l},
          allOrdered kord -> allNotIn knin -> isA i = true -> is_sings sl ->
          backward_flat_nin sl kord knin i l = true -> ninf i l.
      Proof with tea.
        intros i kord knin sl l H1 H2 H3 H4. induction l as [|j l IHl]. intro E. cbn in E. 
        - denin... deif H3... unfold NotIn...
        - deif E as E0.
          { eapply known_nin in E0... denin... deif H3... eapply NotInBoth... }
          deif E as E1.
          { eapply ito_valid in E1... denin... deif H3... rewrite NotInBoth. split... apply NotInl... }
          deif E as E2.
          { eapply ito_valid in E2... denin... deif H3... rewrite NotInBoth. split... apply NotInr... }
          deif E as E3...
          eapply ito_valid in E3... eapply ord_self_nil in E3... unfold ninf. cbn. rewrite E3...
      Qed.
      
      Lemma allOrdered_adds: forall{i js kord},
          allOrdered kord -> sorted (fDenote (i::js)) -> allOrdered (add_knowns i kord js).
      Proof with tea.
        intros i js. induction js as [|j js IHjs]. intros k H1 H2... cbn in *. apply IHjs. 
        - split... eapply sorted_left... rewrite <-app_assoc...
        - eapply sorted_delmid...
      Qed.

      Lemma nilrule : forall a, sorted (aDenote a ++ []) <-> a <# 0.
      Proof with tea.
        intro a. unfold aDenote at 3. rewrite atomics0nil...
      Qed.

      Lemma forward_flat_valid: forall{c l kord},
          allOrdered kord -> sorted (fDenote l) -> forward_flat c l kord = true ->
          exists kord' : Known, allOrdered kord' /\ c kord' = true.
      Proof with tea.
        intros c l. induction l as [|a l IHl]. intros kord H1 H2 H3.
        - eexists...
        - eapply allOrdered_adds in H1... cbn in H3. destruct l as [|b l].
          + cbn in H1. exists (add_known a 0 kord). cbn in H2. apply nilrule in H2. split...
          + eapply IHl... cbn [fDenote] in *. eapply sorted_right...
      Qed.
      
      Lemma allNotIn_add: forall{i l knin},
          allNotIn knin -> ninf i l -> allNotIn (add_knowns i knin l).
      Proof with tea.
        intros i l. induction l as [|j l IHl]. intros knin H1 H2... apply IHl. 1: split...
        unfold nin, ninf in *. deif... deif... cbn in *. rewrite NotInBoth in H2...
      Qed.

      Lemma forward_valid: forall{f kord knin c},
          allOrdered kord -> allNotIn knin -> sfDenote f -> forward c f kord knin = true ->
          exists kord' knin', allOrdered kord' /\ allNotIn knin' /\ c kord' knin' = true.
      Proof with tea.
        intro f. induction f as [i j|l|i l|f1 IHf1 f2 IHf2|f1 IHf1 f2 IHf2| |].
        intros kord knin c H1 H2 H3 H4. 1:apply sflt_norm in H3. cbn in *.
        - exists (add_known i j kord), knin...
        - apply forward_flat_valid in H4 as [k H4]...
          + exists k, knin...
          + rewrite <-flatten_valid...
        - exists kord. exists (add_knowns i knin (flatten l)). repeat split...
          eapply allNotIn_add... apply ninf2nin...
        - destruct H3. eapply IHf1 in H4 as [? []]... eapply IHf2...
        - dorws. destruct H4, H3. eappit. 
        - repeat eexists...
        - repeat eexists...
      Qed.

      Lemma lt_self_valid: forall{sl kord},
          is_sings sl -> allOrdered kord -> lt_self sl kord = true -> False.
      Proof with tea.
        intros sl kord. induction kord as [|[i j] kord IHkord]. intros H0 H1 H2...
        cbn in H2. deif H2 as E.
        - apply ito_valid in H2... eapply ord_self_single... eapply sing_sing...
        - destruct H1...
      Qed.

      Lemma nin_self_valid: forall{sl knin},
          is_sings sl -> allNotIn knin -> nin_self sl knin = true -> False.
      Proof with tea.
        intros sl knin. induction knin as [|[i j] knin IHknin]. intros H0 H1 H2...
        destruct H1 as (N1 & H1). cbn in H2. deif H2 as E. dorws...
        destruct H2 as [H2|H2]... unfold nin in N1. deif N1 as E2...
        deif N1 as E3... cbn in N1. rewrite E2 in N1. apply N1...
      Qed.

      Lemma has_contra_valid: forall{kord knin sl},
          is_sings sl -> allOrdered kord -> allNotIn knin -> has_contra sl kord knin = true ->
          False.
      Proof with tea.
        intros kord knin sl H0 H1 H2. unfold has_contra. dorws. intros [].
        - eapply nin_self_valid...
        - eapply lt_self_valid...
      Qed.

      Lemma backward_valid: forall{sl f kord knin},
          is_sings sl -> allOrdered kord -> allNotIn knin -> backward sl f kord knin = true ->
          sfDenote f.
      Proof with tea.
        intros sl f.
        induction f as [i j|l|i l|f1 IHf1 f2 IHf2|f1 IHf1 f2 IHf2|f1 IHF1 f2 IHf2|].
        intros kord knin H0 H1 H2 H3. 1:apply sflt_norm. cbn in H3. dorws. cbn [sfDenote].
        - destruct H3...
          + eapply ito_valid...
          + eelim has_contra_valid...
        - destruct H3.
          + rewrite flatten_valid. eapply backward_flat_ord_valid...
          + eelim has_contra_valid...
        - deif H3 as E1. 2:eelim has_contra_valid...
          deif H3 as E2. 2:eelim has_contra_valid...
          apply ninf2nin. eapply backward_flat_nin_valid... eapply sing_sing...
        - split. eappit. 
        - destruct H3. (left + right); eappit.
        - intro. apply forward_valid in H3 as [? []]... eappit.
        - eelim has_contra_valid...
      Qed.
    End With_Atomics.

    Fixpoint all_sings(i:nat)(l:list Atom) : list nat :=
      match l with
      | (Aatom _) :: l => i :: all_sings (S i) l
      | _ :: l => all_sings (S i) l
      | nil => nil
      end.

    Lemma all_sings_above:
      forall (l:list Atom) i j, In j (all_sings i l) -> i <= j.
    Proof with tea.
      intro l. induction l as [|[] l IHl]. intros i j H... 
      - destruct H as [H|H]. subst... apply IHl in H... transitivity (S i)...
      - apply IHl in H... transitivity (S i)...
    Qed.

    Lemma all_sings_ok_above:
      forall l i j, In (i + j) (all_sings j l) <-> isA l i = true.
    Proof with tea.
      intro l. induction l as [|b l IHl]. intros i j. split. intro H...
      - destruct i...
      - destruct i.
        + destruct b... cbn in H. apply all_sings_above in H.
          apply PeanoNat.Nat.nle_succ_diag_l in H...
        + rewrite PeanoNat.Nat.add_succ_comm in H. destruct b.
          * destruct H as [H|H]. 2:erewrite IHl in H...
            contradict H. apply PeanoNat.Nat.lt_neq.
            apply PeanoNat.Nat.lt_lt_add_l. apply PeanoNat.Nat.lt_succ_diag_r.
          * erewrite IHl in H...
      - destruct i...
        + destruct b. cbn in * ...
        + cbn. rewrite plus_n_Sm. destruct b.
          1:right. erewrite IHl...
    Qed.

    Lemma all_sings_ok: forall i l, In i (all_sings 0 l) <-> isA l i = true.
    Proof with tea.
      intros i l. rewrite (plus_n_O i) at 1. apply all_sings_ok_above.
    Qed.

    Lemma to_is_sings:
      forall l ats, (forall i, In i l -> isA ats i = true) -> is_sings ats l.
    Proof with tea.
      intro l. induction l as [|n l IHl]. intros ats H. cbn... split.
      - apply H...
      - apply IHl. intros. apply H...
    Qed.

    (*maybe needed in completeness proof*)
    Lemma from_is_sings:
      forall l ats i, is_sings ats l -> In i l -> isA ats i = true.
    Proof with tea.
      intro l. induction l as [|n l IHl]. intros ats i H1 H2. cbn in H2...
      cbn in H1. destruct H1 as (H1 & H3). destruct H2 as [H2|H2]...
      apply IHl...
    Qed.

    Lemma all_sings_is_sings: forall ats, is_sings ats (all_sings 0 ats).
    Proof with tea.
      intros. apply to_is_sings. intros. apply all_sings_ok...
    Qed.

    Lemma do_reflection: forall atomics f,
        let ats := (Latom nil) :: atomics in (*add nil as 0th atom*)
        let singles := all_sings 0 ats in
        if backward singles f [] [] then sfDenote ats f else True.
    Proof with tea.
      intros atomics f. cbn. deif as E... eapply backward_valid in E...
      apply all_sings_is_sings.
    Qed.

  End Reflect_Proof.
  

End Reflection_Proof.

(*Reification tactics*)

Module Reifier.
  Import Reified.
  Import Notations.
  Import Reflection_Proof.

  (*cont is denoted -> max -> xs -> ()*)

  Ltac reifyAtom cont n max a xs axs := idtac;
    lazymatch xs with
    | a::_ => cont n max axs
    | _::?xs => lazymatch n with
                | S ?n => reifyAtom cont n max a xs axs
                | 0 => let n:=constr:(S max) in cont n n constr:(a::axs)
                end
    | _ => fail 999 "reifyAtom invariant broken" max a
    end.
  
  Ltac reifyAvar cont a max xs := reifyAtom cont max max constr:(Aatom a) xs xs.
  Ltac reifyLvar cont a max xs := reifyAtom cont max max constr:(Latom a) xs xs.
  
  Ltac sorta cont dl := cont uconstr:(SF_sorted (LF_app (LF_list 0) (LF_list dl))).
  Ltac sortl cont dl := cont uconstr:(SF_sorted dl).
  Ltac lonel cont dl := cont uconstr:(LF_list dl).
  Ltac opcont cont dop d1 d2 := cont uconstr:(dop d1 d2).
  Ltac oparg2 retac cont dop e2 d1 := retac ltac:(opcont cont dop d1) e2.

  Ltac reifyList cont l max xs := idtac;
    lazymatch l with
    | ?l1 ++ ?l2 => reifyList ltac:(oparg2 reifyList cont uconstr:(LF_app) l2) l1 max xs
    | ?a :: ?l   => reifyAvar ltac:(oparg2 reifyList cont uconstr:(LF_cons) l) a max xs
    | nil       => cont uconstr:(LF_nil) max xs
    | ?l        => reifyLvar ltac:(lonel cont) l max xs
    end.

  Ltac reifyTerm cont e max xs := idtac;
    lazymatch e with
    | ?e1 -> ?e2 => reifyTerm ltac:(oparg2 reifyTerm cont uconstr:(SF_imp) e2) e1 max xs
    | sorted ?l     => reifyList ltac:(sortl cont) l max xs
    | ?e1 /\ ?e2 => reifyTerm ltac:(oparg2 reifyTerm cont uconstr:(SF_and) e2) e1 max xs
    | ?e1 \/ ?e2 => reifyTerm ltac:(oparg2 reifyTerm cont uconstr:(SF_or) e2) e1 max xs
    | ?a < ?b   => reifyAvar ltac:(oparg2 reifyAvar cont uconstr:(SF_lt) b) a max xs
    | ?a ∉ ?l   => reifyAvar ltac:(oparg2 reifyList cont uconstr:(SF_notin) l) a max xs
    | ~ ?a ∈ ?l => reifyAvar ltac:(oparg2 reifyList cont uconstr:(SF_notin) l) a max xs
    | _         => cont uconstr:(SF_skip e) max xs
    end.
  
  Ltac reverse xs ys :=
    lazymatch xs with
    | ?h::?xs => reverse xs constr:(h::ys)
    | _ => ys
    end.
  
  Ltac reify_and_reflect finish := idtac;
    let X := lazymatch type of (_:Ordered _) with
               Ordered ?A => A
             end in
    lazymatch goal with
      |- ?G =>
      let cont d max xs :=
          let atoms := reverse xs constr:(nil:list (@Atom X))
          in 
          lazymatch atoms with
            (*remove leading nil so that reflector can put it back and prove its there*)
          | _ :: ?atoms => finish atoms d
          end
      in
      (*atom index 0 is reserved for nil, so start xs with Latom nil:*)
      reifyTerm cont G 0 constr:([@Latom X nil])
    end.
  
  (*Solver tactic, X is the element type:*)

  Ltac do_reverts :=
    repeat (*revert Props only*)
      match goal with
      | H : ?T |- _ => let tT:=type of T in constr_eq tT Prop; revert H
      end.
  
  Ltac ss finish :=
    intros; do_reverts;
    reify_and_reflect finish || fail "solve_sorted failed on goal".
  
  Ltac finish atoms f :=
    abstract (vm_cast_no_check (do_reflection atoms f)).

  Ltac finishdebug atoms f :=
    let a:=fresh "atoms" in
    let r:=fresh "reified" in
    let d:=fresh "denoted" in
    pose ((Latom nil)::atoms) as a; pose f as r;
    pose (sfDenote a r) as d.
  
End Reifier.

Ltac solve_sorted := idtac; Reifier.ss Reifier.finish.
Ltac debug_solve_sorted := idtac; Reifier.ss Reifier.finishdebug.

Unset Mangle Names.

Module Examples.

  Context {A : Set}.
  Context {ordA : Ordered A}.
  Import Notations.

  Notation ss := ltac:(solve_sorted) (only parsing).

  Implicit Types a b c d e f : A.
  Implicit Types l p q r s t u v w x z: list A.

  (*check that solve_sorted fails prior to Qed*)
  Example invalid: forall l1 l2, sorted l1 -> sorted l2.
  Fail solve_sorted.
  Abort.

  Example realeasy: forall a l, sorted (a::l) -> sorted (a::l) := ss.
  
  Example nolistatoms: forall a b c d e f,
      sorted (a::(b::(c::d::nil)++e::nil)++f::nil) -> sorted(a::c::f::nil).
  Proof.
    solve_sorted.
  Qed.
  
  Example listsonly: forall p q r, sorted(p++q++r) -> sorted(p++r).
  Proof.
    solve_sorted.
  Qed.

  Example ltonly: forall a b, a<b -> a<b.
  Proof.
    solve_sorted.
  Qed.

  Example trans: forall a b c, a<b -> b<c -> a<c.
  Proof.
    solve_sorted.
  Qed.
  
  Example interesting:
    forall a b p q r, sorted(a::p++q++r) -> sorted(p++r++[b]) -> sorted(q++[b]) -> a<b ->
                 sorted(p++q++r++[b]).
  Proof.
    solve_sorted.
  Qed.

  Example big:
    forall p q r s t u v a b c d e f l,
      sorted(p++[a]++(q++[b])++r++l++([c]++(s++[d])++t++[e])++(u++[f])++v) ->
      sorted(q++([c]++t)++[e]++v).
  Proof.
    solve_sorted.
  Qed.

  (*cases like this degenerate test are where the (nil,l) known kludge is needed*)
  Example degenerate: forall l, sorted l -> sorted l.
  Proof.
    solve_sorted.
  Qed.

  (*proof by contradiction, by finding a cycle among singletons*)
  Example contra2: forall a b c, a<b -> b<a -> a<c.
  Proof.
    solve_sorted.
  Qed.

  Example bigger:
    forall p q r s t u v w x y z a b c,
      sorted(p++q++r++s++t++[a]) -> a<b -> a<c -> sorted(b::u++v++w) ->
      sorted(c::x++y) -> sorted(c::x++z) /\ sorted(c::y++z) ->
      sorted(u++v++w++[c]) \/ b<c ->
      b<c \/ sorted(p++q++r++s++t++u++v++w++x++y++z) /\ sorted(q++s++u++w++y).
  Proof.
    solve_sorted.
  Qed.

  (*determine that some lists must be nil*)
  Example pnil: forall p a b,
      sorted(p++[a]) -> sorted(a::p) -> sorted(p++b::p).
  Proof.
    solve_sorted.
  Qed.

  Example notin1: forall a l, sorted(a::l) -> a ∉ l.
  Proof.
    solve_sorted.
  Qed.

  Example notin2: forall a p q, a ∉ p -> a ∉ q -> a ∉ (p++q).
  Proof.
    solve_sorted.
  Qed.

  Example notin3: forall a b l, sorted (l++[a]) -> a<b -> b ∉ l.
  Proof.
    solve_sorted.
  Qed.

  Example notin4: forall a, ~ a ∈ [a] -> False.
  Proof.
    solve_sorted.
  Qed.

  Example notin5: forall a b c l1 l2,
      b ∉ l2 -> a<c -> c<b -> sorted(l1++a::l2) -> b ∉ (l1++a::l2).
  Proof.
    solve_sorted.
  Qed.

  Example notin6: forall a b l1 l2,
      b ∉ l2 -> sorted (b::l1) -> sorted(l1++a::l2) -> a<b -> b ∉ (l1++a::l2).
  Proof.
    solve_sorted.
  Qed.

  Example notin7: forall a l, sorted (l++l) -> a ∉ l.
  Proof.
    solve_sorted.
  Qed.

  Example notin8: forall a b l, sorted (l++[b]) -> sorted(b::l) -> a ∉ l.
  Proof.
    solve_sorted.
  Qed.

  Example not_strict_total: forall a b, a ∉ [b] -> a<b \/ b<a.
  Proof.
     (*Ord is a Strict Order but not necessarily a Strict Total Order, so we do not have access to a decidable comparison.  If we did, it would be difficult to incorporate into the reflection procedure.*)
    Fail solve_sorted.
  Abort.

  Example nil_omitted: forall a d, a < d -> sorted(a::d::nil).
  Proof.
    (*fails if nil isn't reified properly (by LF_nil, not LF_list 0)*)
    solve_sorted.
  Qed.

  Example oops: forall l, sorted(nil++l) -> sorted l.
  Proof.
    solve_sorted.
  Qed.

  Example withfun: forall l (P:A -> Prop), sorted l -> sorted l.
  Proof.
    solve_sorted.
  Qed.

End Examples.

(* Local Variables: *)
(* company-coq-local-symbols: (("++" . ?⧺) ("..." . ?…) ("sorted" . ?⊿) ("<#" . ?⧏) ("Known" . ?Ǩ) ("tea" . ?🍵)) *)
(* End: *)
