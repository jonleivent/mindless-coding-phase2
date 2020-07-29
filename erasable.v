
Require Import mindless.hypiter.
Require Import mindless.factorevars.

Global Set Keep Proof Equalities.

Inductive Erasable(A : Set) : Prop :=
  erasable: A -> Erasable A.

Arguments erasable [A] _.

Hint Constructors Erasable : core.

Scheme Erasable_elim := Induction for Erasable Sort Prop.

Module ErasableNotation.
  Declare Scope Erasable_scope.
  Notation "## T" := (Erasable T) (at level 1, format "## T") : Erasable_scope.
  Notation "# x" := (erasable x) (at level 1, format "# x") : Erasable_scope.
  Open Scope Erasable_scope.
End ErasableNotation.

Import ErasableNotation.

(*This Erasable_inj axiom is the key enabler of erasability beyond
what Prop already provides.  Note that it can't be mixed with
proof irrelevance.*)
Axiom Erasable_inj : forall {A : Set}{a b : A}, #a=#b -> a=b.

Require Setoid. (*needed for Erasable_rw users*)

Lemma Erasable_rw : forall (A: Set)(a b : A), (#a=#b) <-> (a=b).
Proof.
  intros A a b.
  split.
  - apply Erasable_inj.
  - congruence.
Qed.

Create HintDb unerase_rws discriminated.
Hint Rewrite Erasable_rw : unerase_rws.

Create HintDb unerase_unfolds discriminated.
Create HintDb lift_unfolds discriminated.

Ltac unerase_hyp H :=
  autounfold with unerase_unfolds in H;
  autorewrite with unerase_rws in H;
  tryif has_value H
  then
    let V:=get_value H in
    let R:=fresh in
    let E:=fresh in
    remember V as R eqn:E;
    autorewrite with unerase_rws in E;
    lazymatch type of H with
    | ## _ =>
      destruct R as [R];
      rewrite Erasable_rw in E;
      let H':=fresh in
      set (H':=R) in H;
      unfold H in *;
      clear H;
      rename H' into H
    | _ => idtac
    end;
    subst R
  else
    lazymatch type of H with
    | ## _ =>
      let H':=fresh H in
      destruct H as [H'];
      clear H;
      rename H' into H
    | # _ = # _ => apply Erasable_inj in H as ?
    | _ => idtac
    end.

Tactic Notation "unerase" constr(H) := unerase_hyp H.

Ltac try_unerase_hyp H := try (unerase_hyp H).

Ltac unerase_hyps := allhyps_introing try_unerase_hyp.

Ltac check_in_prop :=
  lazymatch goal with
    |- ?G =>
    let U:=type of G in
    first [constr_eq U Prop
          |fail 1 "check_in_prop:" G "is not a Prop"]
  end.

Ltac unerase_internal' :=
  autounfold with unerase_unfolds;
  unerase_hyps;
  autorewrite with unerase_rws;
  try apply erasable.

Create HintDb lift_rws discriminated.

Hint Rewrite -> Erasable_rw : lift_rws.

Ltac unerase_do_rws :=
  idtac;
  autorewrite with lift_rws in *.

Ltac unerase_internal :=
  repeat lazymatch goal with
         | H : ## _ |- _ =>
           first [destruct H as [H]
                 |let x:=fresh in destruct H as [x]; clear H; rename x into H]
         end;
  cbn in *;
  autounfold with lift_unfolds in *;
  unerase_do_rws;
  subst.

Tactic Notation "unerase" :=
  intros;
  tryif check_in_prop
  then unerase_internal
  else rewrite ?Erasable_rw in *.

Local Ltac solve_erasable_exists :=
  intros T x P;
  split;
  [ intros (y & H1 & H2);
    first[apply Erasable_inj in H1|apply Erasable_inj in H2];
    subst;
    assumption
  | intro H;
    exists x;
    tauto].

Lemma Erasable_exists_rw1 :
  forall (T : Set) (x : T) (P : T -> Prop), (exists (y : T), #y = #x /\ P y) <-> P x.
Proof. solve_erasable_exists. Qed.

Lemma Erasable_exists_rw2 :
  forall (T : Set) (x : T) (P : T -> Prop), (exists (y : T), #x = #y /\ P y) <-> P x.
Proof. solve_erasable_exists. Qed.

Lemma Erasable_exists_rw3 :
  forall (T : Set) (x : T) (P : T -> Prop), (exists (y : T), P y /\ #y = #x) <-> P x.
Proof. solve_erasable_exists. Qed.

Lemma Erasable_exists_rw4 :
  forall (T : Set) (x : T) (P : T -> Prop), (exists (y : T), P y /\ #x = #y) <-> P x.
Proof. solve_erasable_exists. Qed.

Hint Rewrite Erasable_exists_rw1 Erasable_exists_rw2 Erasable_exists_rw3 Erasable_exists_rw4 : unerase_rws.

(* Erasable+Prop is a monad, and appE is application within that monad
of lifted functions.  But, the result would then need the "f $ x $ y"
syntax, and would also make operators ugly... *)
Definition appE{T1 T2 : Set}(f : ##(T1 -> T2))(x : ## T1) : ## T2.
Proof.
  destruct f as [f].
  destruct x as [x].
  constructor.
  exact (f x).
Defined.

(*Infix "$" := appE (left associativity, at level 98) : E_scope.*)

(* ... So, instead of lifting functions with # alone, we use lifters
that leave the normal application syntax intact.  This means we need
to do a little more work to lift, but end up with a much more readable
result. *)

Definition lift1{A B : Set}(f : A -> B)(a : ##A) : ##B :=
  match a with
  | erasable a => # (f a)
  end.

Lemma liftrw1: forall {A B : Set}{f : A -> B}{a : A}, (lift1 f) # a = # (f a).
Proof.
  intros. reflexivity.
Qed.

Definition lift2{A B C : Set}(f : A -> B -> C)(a : ##A)(b : ##B) : ##C :=
  match a, b with
  | erasable a, erasable b => # (f a b)
  end.

Lemma liftrw2: forall{A B C : Set}{f : A -> B -> C}{a : A}{b : B},
    (lift2 f) # a # b = # (f a b).
Proof.
  intros. reflexivity.
Qed.

(* For Props, instead of a normal lifting of the entire signature,
which would result in ##Prop type instead of a more usable Prop type,
the Prop is wrapped in an existential to accept the erasable arg. *)
Definition liftP1{A : Set}(p : A -> Prop)(ea : ##A) : Prop :=
  exists (a : A), #a=ea /\ p a.

Lemma liftrwP1 : forall {A : Set}{p : A -> Prop}{ea : A},
    (liftP1 p) # ea <-> p ea.
Proof.
  intros. unfold liftP1. split.
  - intros (a & E & H). apply ->Erasable_rw in E. subst. exact H.
  - intro H. exists ea. tauto.
Qed.

Hint Rewrite @liftrwP1 : lift_rws.

Definition liftP2{A B : Set}(p : A -> B -> Prop)(ea : ##A)(eb : ##B) : Prop :=
  exists (a : A), #a=ea /\ exists (b : B), #b=eb /\ p a b.

Lemma liftrwP2: forall{A B : Set}{p : A -> B -> Prop}{ea : A}{eb : B},
    (liftP2 p) #ea #eb <-> p ea eb.
Proof.
  intros. unfold liftP2. split.
  - intros (a & Ea & b & Eb & H). apply ->Erasable_rw in Ea. apply ->Erasable_rw in Eb.
    subst. exact H.
  - intro H. exists ea. split; [reflexivity|]. exists eb. tauto.
Qed.

Hint Rewrite @liftrwP2 : lift_rws.

Hint Unfold lift1 lift2 liftP1 liftP2 : unerase_unfolds.

(*Lifting preserves well-foundedness - useful for well_founded_induction*)

Require Import Coq.Init.Wf.

Lemma Ewf : forall {A:Set}{R : A -> A -> Prop}, well_founded R -> well_founded (liftP2 R).
Proof.
  intros A R wfR. unfold well_founded. intro b. destruct b as [b].
  induction b as [b IHb] using (well_founded_induction wfR).
  apply Acc_intro. intros. unerase. apply IHb. assumption.
Qed.

Lemma Ewfof : forall {A B:Set}{R : A -> A -> Prop}(f : B -> A),
    well_founded R -> well_founded (fun x y => (liftP2 R) ((lift1 f) x) ((lift1 f) y)).
Proof.
  intros A B R f wfR. unfold well_founded. intro b. unerase b.
  remember (f b) as fb eqn:E. revert b E.
  induction fb as [fb IHb] using (well_founded_induction wfR). intros b ->.
  apply Acc_intro. intros a Rfafb. unerase. eapply IHb.
  - eassumption.
  - reflexivity.
Qed.

(*Lifting preserves decidability*)

Lemma Edec : forall {A:Set}, (forall (x y:A), {x = y} + {x <> y}) -> forall (x y:A), {#x = #y} + {#x <> #y}.
Proof.
  intros A H x y.
  specialize (H x y).
  destruct H.
  - subst. tauto.
  - right. unerase. tauto.
Qed.

Lemma EPdec : forall {A:Set}, (forall (x y:A), x = y \/ x <> y) -> forall (x y:##A), x = y \/ x <> y.
Proof.
  intros A H x y.
  unerase.
  apply H.
Qed.

Require Coq.Logic.Eqdep_dec.

Lemma Eeq_proofs_unicity : forall {A:Set}, (forall x y:A, x = y \/ x <> y) -> forall (x y:##A) (p1 p2 : x = y), p1 = p2.
Proof.
  intros A H.
  apply Eqdep_dec.eq_proofs_unicity.
  apply EPdec.
  exact H.
Qed.
