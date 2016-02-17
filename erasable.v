(***********************************************************************

Copyright (c) 2016 Jonathan Leivent

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

***********************************************************************)

Require Import hypiter.
Require Import factorevars.

Inductive Erasable(A : Set) : Prop :=
  erasable: A -> Erasable A.

Arguments erasable [A] _.

Hint Constructors Erasable.

Scheme Erasable_elim := Induction for Erasable Sort Prop.

Module ErasableNotation.
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

Hint Rewrite Erasable_rw : unerase_rws.

Ltac unerase_hyps :=
  let f H :=
      try
      (autorewrite with unerase_rws in H;
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
          | _ => idtac
          end) in
  hyps => rloop f.

Ltac check_in_prop :=
  lazymatch goal with
    |- ?G =>
    let U:=type of G in
    first [constr_eq U Prop
          |fail 1 "check_in_prop:" G "is not a Prop"]
  end.

Ltac unerase_internal :=
   unerase_hyps;
   autorewrite with unerase_rws;
   try apply erasable.

Ltac unerase :=
  intros;
  tryif check_in_prop
  then unerase_internal
  else rewrite ?Erasable_rw in *.

(* Erasable+Prop is a monad, and appE is application within that monad
of lifted functions.  But, the result would then need the "f $ x $ y"
syntax, and would also make operators ugly... *)
Definition appE{T1 T2 : Set}(f : ##(T1 -> T2))(x : ## T1) : ## T2.
Proof.
  unerase.
  exact (f x).
Defined.

(*Infix "$" := appE (left associativity, at level 98) : ELN_scope.*)

(* ... So, instead of lifting functions with # alone, we use lifters
that leave the normal application syntax intact.  This means we need
to do a little more work to lift, but end up with a much more readable
result. *)
Definition lift1{A B : Set}(f : A -> B)(a : ##A) : ##B.
Proof.
  unerase.
  exact (f a).
Defined.

Definition lift2{A B C : Set}(f : A -> B -> C)(a : ##A)(b : ##B) : ##C.
Proof.
  unerase.
  exact (f a b).
Defined.

(* For Props, instead of a normal lifting of the entire signature,
which would result in ##Prop type instead of a more usable Prop type,
the Prop is wrapped in an existential to accept the erasable arg. *)
Definition liftP1{A : Set}(p : A -> Prop)(ea : ##A) : Prop :=
  exists (a : A), #a=ea /\ p a.

Definition liftP2{A B : Set}(p : A -> B -> Prop)(ea : ##A)(eb : ##B) : Prop :=
  exists (a : A), #a=ea /\ exists (b : B), #b=eb /\ p a b.
