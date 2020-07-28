
From Coq Require Export Lists.List.
Require Export mindless.ordered.
Require Export mindless.solvesorted.
Require Export mindless.erasable.
Export ErasableNotation.
Export Notations.
Require Import mindless.utils.

Notation " [ ] " := nil (format "[ ]") : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.

Global Opaque NotIn.

Section defs.
  Context {A : Set}.

  Definition Eapp := (lift2 (@app A)).

  Lemma Eapp_rw :
    forall (x y : list A), (Eapp #x #y) = #(app x y).
  Proof.
    unfold Eapp.
    unerase.
    tauto.
  Qed.

  Definition ENotIn(x : A) := liftP1 (NotIn x).

  Lemma ENotIn_rw :
    forall (a : A)(x : list A), ENotIn a #x <-> NotIn a x.
  Proof.
    unfold ENotIn.
    unerase.
    tauto.
  Qed.

  Context {ordA : Ordered A}.
  
  Definition Esorted := (liftP1 sorted).
  
  Lemma Esorted_rw : 
    forall (x : list A), Esorted #x <-> sorted x.
  Proof.
    unfold Esorted.
    unerase.
    tauto.
  Qed.

End defs.

(*Global Opaque Eapp ENotIn.*)
Hint Unfold Eapp ENotIn Esorted : lift_unfolds.

Hint Rewrite @Esorted_rw @ENotIn_rw @Eapp_rw : unerase_rws.

Lemma lnenil : forall {A}(d : A)(lf rf : list A), (lf++d::rf)%list <> nil.
Proof.
  dintros.
  intro H.
  eapply app_eq_nil in H as [? ?].
  discriminate.
Qed.

Lemma lnenilrw : forall {A}(d : A)(lf rf : list A), ((lf++d::rf)%list = nil) <-> False.
Proof.
  dintros.
  split.
  - intro.
    eapply lnenil.
    eassumption.
  - contradiction.
Qed.

Lemma red_app : forall {A}(a : A)(l : list A), ([a]++l)%list = (a::l)%list.
Proof.
  cbn.
  reflexivity.
Qed.

Hint Rewrite @red_app @lnenilrw : bang_rws.

(* Some nice syntax for erasable lists.  Note the use of ^x instead
  of [x] - because for some reason [x] wouldn't work in all cases. *)
Declare Scope E_scope.
Infix "++" := Eapp (right associativity, at level 60) : E_scope.
Notation " [ ] " := (# nil) : E_scope.
Notation " [ x ] " := (# (cons x nil)) : E_scope.
Bind Scope E_scope with Erasable.
Bind Scope list_scope with list.
Open Scope E_scope.

Section EL_lemmas.
  Context {A : Set}.

  Notation EL := (## (list A)).

  Lemma Eapp_assoc: forall {p q r : EL}, (p++q)++r = p++(q++r).
  Proof. 
    intros.
    unerase.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  Lemma group3Eapp: forall (p q r s : EL), p++q++r++s = (p++q++r)++s.
  Proof.
    intros.
    rewrite ?Eapp_assoc.
    reflexivity.
  Qed.

  Lemma Eapp_nil_l : forall (l : EL), []++l = l.
  Proof.
    unerase.
    reflexivity.
  Qed.
  
  Lemma Eapp_nil_r : forall (l : EL), l++[] = l.
  Proof.
    unerase.
    intros.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma fnenil1 : forall (d : A), [d] <> [].
  Proof.
    unerase.
    discriminate.
  Qed.

  Lemma fnenil2 : forall (d : A)(rf : EL), [d]++rf <> [].
  Proof.
    unerase.
    intro H.
    eapply app_eq_nil in H.
    intuition discriminate.
  Qed.

  Lemma fnenilright : forall (lf rf : EL), rf <> [] -> lf++rf <> [].
  Proof.
    unerase.
    intro H'.
    eapply app_eq_nil in H'.
    intuition discriminate.
  Qed.

  Lemma fnenilrw : forall (d : A)(lf rf : EL), lf++[d]++rf = [] <-> False.
  Proof.
    dintros.
    unerase.
    cbn.
    rewrite lnenilrw.
    tauto.
  Qed.

End EL_lemmas.

Ltac reassociate_step :=
  lazymatch goal with
    |- context [?X ++ ?Y] =>
    let V:=fresh in
    set (V:=X++Y);
    let H:=fresh in
    lazymatch get_value V with
      ?A ++ ?B ++ ?C =>
      assert (((A++B)++C) = V) as H by apply Eapp_assoc;
      clearbody V
    end;
    lazymatch type of H with
      ?A ++ ?B = V =>
      let V':=fresh in
      set (V':=A) in H;
      let H':=fresh in
      assert (V'=A) as H' by reflexivity;
      rewrite ?Eapp_assoc in H';
      clearbody V';  
      subst V'
    end;
    subst V
  end.

Ltac reassoc :=
  rewrite ?Eapp_assoc;
  let rec f := idtac + (reassociate_step; f) in f.

Tactic Notation "assoc" integer(n) :=
  rewrite ?Eapp_assoc;
  do n reassociate_step.

Ltac rootify d :=
  reassoc;
  (lazymatch goal with
      |- context [?X ++ ?Y] =>
      lazymatch constr:(X ++ Y) with
        _ ++ [d] ++ _ => idtac
      end
    end).

Ltac fnenil :=
  let rec f := (idtac + (apply fnenilright; f)) in
  let rec g := rewrite ?Eapp_assoc; f; solve [apply fnenil2 | apply fnenil1] in
  match goal with
  | |- ([] = [])%type => reflexivity
  | H : ([] <> [])%type |- _ => contradict H; reflexivity
  | |- (_ <> [])%type => g
  | |- ([] <> _)%type => apply not_eq_sym; g
  | H : (_ = [])%type |- _ => contradict H; g
  | H : ([] = _)%type |- _ => symmetry in H; contradict H; g
  end.
