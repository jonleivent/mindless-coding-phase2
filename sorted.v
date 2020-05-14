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

(* Useful lemmas about sorted lists. *)

Require Export Coq.Lists.List.
Import ListNotations.

Require Export mindless.ordered.
Require Export Coq.Sorting.Sorted.

Notation sorted := (LocallySorted lt).

Set Default Goal Selector "all".

Section defs.
  Context {A : Set}.
  Context {A_ordered : Ordered A}.

  Local Ltac triv := subst; try solve [eassumption | constructor; eassumption].

  Lemma sortedl : forall {l1 l2 : list A}, sorted (l1++l2) -> sorted l1.
  Proof with triv.
    induction l1 as [|a l1 IHl1]... 
    intros l2 H. destruct l1... 
    inversion H... 
    constructor...
    eapply IHl1...
  Qed.

  Lemma sortedr : forall {l1 l2 : list A}, sorted (l1++l2) -> sorted l2.
  Proof with triv.
    induction l1 as [|a l1 IHl1].
    intros l2 H... destruct l1.
    inversion H...
    eapply IHl1...
  Qed.

  Lemma sortedtail : forall {l : list A}{a : A}, sorted (a::l) -> sorted l.
  Proof with triv.
    intros l a H. inversion H...
  Qed.

  Lemma sortcomb : forall {l1 l2 : list A}{a : A},
                     sorted(l1++[a]) -> sorted(a::l2) -> sorted(l1++a::l2).
  Proof with triv.
    induction l1 as [|a l1 IHl1]. intros l2 ? H1 H2...
    destruct l1. simpl in *. constructor... inversion H1... apply IHl1...
  Qed.

  Lemma sortins : forall {l1 l2 l3 : list A}{a b : A},
                    sorted(l1++a::l2) ->
                    sorted(l2++b::l3) -> lt a b ->
                    sorted(l1++a::l2++b::l3).
  Proof with triv.
    induction l1 as [|a l1 IHl1]. intros l2 l3 ? ? H H0 H1.
    - destruct l2... inversion H... 
    - destruct l1. simpl in *.
      inversion H. subst. constructor... eapply IHl1...
  Qed.

  Lemma desort : forall {l1 l2 : list A}{a b : A},
                     sorted (a::l1++b::l2) -> lt a b.
  Proof with triv.
    induction l1 as [|a l1 IHl1]. intros ? ? ? H. inversion H... 
    transitivity a... eapply IHl1...
  Qed.

  Lemma sortedm : forall {l1 l2 l3 : list A},
                    sorted (l1++l2++l3) -> sorted (l1++l3).
  Proof with triv.
    induction l1 as [|a l1 IHl1]. intros l2 l3 H.
    - eapply sortedr...
    - destruct l1.
      + destruct l3... constructor.
        * do 2 apply sortedr in H...
        * apply desort in H...
      + inversion H... simpl. constructor... eapply IHl1...
  Qed.

  Definition NotIn(x : A)(l : list A) := ~In x l.

  Lemma NotInNil: forall (x : A), NotIn x [].
  Proof.
    apply in_nil.
  Qed.

  Lemma NotInCons: forall {l : list A}{x d : A},
                     lt x d -> sorted (d::l) -> NotIn x (d::l).
  Proof with triv.
    induction l as [|y l IHl]. intros x d H H0.
    - destruct 1... apply irreflexivity in H...
    - inversion H0. destruct 1. subst.
      + apply irreflexivity in H...
      + eapply (IHl x y)... transitivity d...
  Qed.

  Lemma NotInl: forall {x d : A}{l1 l2:list A},
                  NotIn x l1 -> lt x d -> sorted(l1++d::l2) ->
                  NotIn x (l1++d::l2).
  Proof with triv.
    induction l1 as [|y l1 IHl1]. intros l2 H H0 H1.
    - apply NotInCons...
    - destruct 1 as [|H2]. subst.
      + elim H. apply in_eq.
      + eapply IHl1 in H2...
        * intro. elim H...
        * simpl in H1. apply sortedtail in H1...
  Qed.

  Lemma NotInr: forall {x d : A}{l1 l2 : list A},
                  NotIn x l2 -> lt d x -> sorted(l1++d::l2) ->
                  NotIn x (l1++d::l2).
  Proof with triv.
    induction l1 as [|y l1 IHl1]. intros l2 H H0 H1 []. subst.
    - eapply irreflexivity...
    - eapply H...
    - apply desort in H1.
      eapply irreflexivity...
      eapply (transitivity H1 H0).
    - eapply IHl1... simpl in H1. apply sortedtail in H1...
  Qed.

End defs.

(* Local Variables: *)
(* company-coq-local-symbols: (("++" . ?⧺) ("..." . ?…) ("sorted" . ?⊿)) *)
(* End: *)
