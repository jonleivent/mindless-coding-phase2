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

(* A crude "decision" procedure over certain kinds of sorted lists -
those with singleton deliminters between sublists, such as
sorted(p++[x]++q++[y]++r).  It has some limited ability to work even
in cases without such singleton delimiters.  One advantage is that
associativity is disposed of by decomposing sorted lists into pairs
over the "slt" and "lts" relations (singleton-lt and lt-singleton,
respectively).  If needed, it could probably be made into a full
decision procedure by noting that a term such as sorted(p++q) can be
converted into sorted(p) and sorted(p++[x]++q) by destructing q. *)

Require Import mindless.sorted.
Import ListNotations.

Set Default Goal Selector "all".

Section defs.
  Context {A : Set}.
  Context {ordA : Ordered A}.

  Infix "<" := lt (at level 70) : list_scope.

  Inductive slt : A -> list A -> Prop :=
  | slt0(a : A) : slt a []
  | slt1(a b : A) : a < b -> slt a [b]
  | sltN(a b : A)(l : list A) : a < b -> slt b l -> slt a (b::l).

  Infix "!<" := slt (at level 70) : list_scope.

  Local Ltac triv := try solve [eassumption | constructor].

  Lemma sorted2slt : forall l a, sorted (a::l) <-> a !< l.
  Proof with triv.
    induction l as [|? ? IHl]. split. intro H.
    constructor. inversion H... apply IHl...
  Qed.

  Inductive lts : list A -> A -> Prop :=
  | lts0(a : A) : lts [] a
  | lts1(a b : A) : a < b -> lts [a] b
  | ltsN(a b : A)(l : list A) : a < b -> lts l b -> a !< l -> lts (a::l) b.

  Infix "<!" := lts (at level 70) : list_scope.

  Lemma sorted2lts : forall l a, sorted(l++[a]) <-> l <! a.
  Proof with triv.
    induction l as [|? l IHl]. split... intro H.
    - constructor. 
      + apply desort in H...
      + apply IHl. inversion H...
      + apply sorted2slt. eapply sortedl...
    - destruct l. simpl. constructor...
      + inversion H...
      + apply IHl. inversion H...
      + inversion H as [ | |_ ? _ _ _ []]...
  Qed.

  Local Ltac appify H := repeat match type of H with
                                  context [?a :: ?X] => 
                                  first [constr_eq X (@nil A); fail 1
                                        |change (a::X) with ([a]++X) in H] end.
  
  Local Ltac appify_goal := repeat match goal with 
                                     |- context [?a :: ?X] => 
                                     first [constr_eq X (@nil A); fail 1
                                           |change (a::X) with ([a]++X)] end.

  Lemma sorted2both : forall l1 l2 a, sorted(l1++a::l2) <-> l1 <! a /\ a !< l2.
  Proof with triv.
    intros. rewrite <- sorted2slt, <- sorted2lts. repeat split.
    - appify H. rewrite app_assoc in H. apply sortedl in H...
    - apply sortedr in H...
    - intros (? & ?). eapply sortcomb... 
  Qed.

  Lemma redlts : forall l a b, (a::l) <! b <-> a !< l /\ l <! b /\ a < b.
  Proof with triv.
    split.
    - intros H. inversion H. repeat split... 
    - intros (? & ? & ?). constructor...
  Qed.

  Lemma redslt : forall l a b, a !< (b::l) <-> a < b /\ b !< l.
  Proof with triv.
    split.
    - intros H. inversion H. repeat split...
    - intros (? & ?). constructor...
  Qed.

  Lemma rwslts : forall a b l l1, a !< l++b::l1 <-> a !< l /\ a < b /\ l <! b /\ b !< l1.
  Proof.
    intros a b l l1. rewrite <- sorted2slt. split.
    - intro H. appify H. 
      pose proof (sortedr H) as H1.
      pose proof (sortedr H1) as H2. simpl in H2. rewrite sorted2slt in H2.
      rewrite app_assoc in H1. apply sortedl in H1. rewrite sorted2lts in H1.
      pose proof (desort H) as H3.
      rewrite app_assoc in H. apply sortedl in H. simpl in H. rewrite sorted2slt in H.
      repeat split. assumption.
    - intros (H1 & H2 & H3).
      rewrite <- sorted2slt in H1.
      rewrite <- sorted2both in H3.
      apply (@sortins _ _ [] l l1 a b H1 H3 H2).
  Qed.

  Lemma slt_trans : forall a b l, a < b -> b !< l -> a !< l.
  Proof with triv.
    intros ? b ? ? H. inversion H... constructor... transitivity b...
  Qed.

  Lemma lts_trans : forall l a b, a < b -> l <! a -> l <! b.
  Proof with triv.
    induction l as [|a b IHl]. intros a0 b0 H0 H1...
    constructor. 1: transitivity a0... inversion H1... eapply IHl...
  Qed.

  Lemma sorted2both2 : forall l0 l1 l2 a, sorted (l0++l1++a::l2) <-> (l0++l1) <! a /\ a !< l2.
  Proof.
    intros. rewrite app_assoc. apply sorted2both.
  Defined.

  Lemma ltssorted : forall l a, l <! a -> sorted l.
  Proof with triv.
    intros ? ? []... rewrite sorted2slt...
  Qed.

  Lemma sltsorted : forall l a, a !< l -> sorted l.
  Proof with triv.
    intros ? ? []... rewrite sorted2slt...
  Qed.

  Lemma ltsleft : forall l0 l1 a, (l0++l1) <! a -> l0 <! a.
  Proof.
    intros ? ? ? H.
    rewrite <- sorted2lts in *.
    rewrite <- app_assoc in H.
    apply (sortedm H).
  Qed.

  Lemma ltsright : forall l0 l1 a, (l0++l1) <! a -> l1 <! a.
  Proof.
    intros ? ? ? H.
    rewrite <- sorted2lts in *.
    rewrite <- app_assoc in H.
    apply (sortedr H).
  Defined.

  Lemma ltsmk2 : forall l0 l1 a, sorted(l0++l1) -> l0 <! a -> l1 <! a -> (l0++l1) <! a.
  Proof with triv.
    induction l0 as [|? ? IHl].
    - intros. simpl...
    - intros ? ? ? H ?. simpl in *. constructor...
      + inversion H...
      + apply IHl...
        * eapply sortedtail...
        * inversion H...
      + apply sorted2slt...
  Qed.

  Lemma ltssplit : forall l0 l1 a, (l0++l1) <! a <-> sorted(l0++l1) /\ l0 <! a /\ l1 <! a.
  Proof with triv.
    intros. split.
    - intro H. repeat split.
      + eapply ltssorted... 
      + eapply ltsleft...
      + eapply ltsright...
    - intros (? & ? & ?). apply ltsmk2...
  Qed.

  Lemma sltleft: forall l0 l1 a, a !< (l0++l1) -> a !< l0.
  Proof.
    intros ? ? ? H.
    rewrite <- sorted2slt in *.
    appify H. rewrite app_assoc in H.
    apply (sortedl H).
  Qed.   

  Lemma sltright: forall l0 l1 a, a !< (l0++l1) -> a !< l1.
  Proof.
    intros ? ? ? H.
    rewrite <- sorted2slt in *.
    appify H. apply (sortedm H).
  Qed.

  Lemma ltsright1 : forall l a b, a !< ([b]++l) -> a < b.
  Proof with triv.
    intros ? ? ? H. inversion H...
  Qed.

  Lemma sltlts2sorted : forall a p q, p <! a -> a !< q -> sorted (p++q).
  Proof.
    intros a p q H H0.
    assert (sorted (p++[a]++q)) as H1.
    - apply sorted2both. tauto.
    - apply (sortedm H1).
  Qed.
  
  Lemma sltapp : forall q r a b, a !< q -> q <! b -> b !< r -> a < b -> a !< q ++ r.
  Proof.
    intros q r a b H H0 H1 H2.
    assert (q <! b /\ b !< r) as H3 by tauto.
    rewrite <- sorted2both in H3.
    rewrite <- sorted2slt in *.
    pose proof (@sortins _ _ [] q r a b H H3 H2) as H4.
    simpl in H4. appify H4.
    appify_goal. rewrite app_assoc. eapply sortedm. rewrite <- app_assoc.
    eexact H4.
  Qed.

  Lemma lts2lt : forall a b, [a] <! b <-> a < b.
  Proof with triv.
    split. intro H.
    - inversion H...
    - constructor...
  Qed.

  Lemma slt2lt : forall a b, a !< [b] <-> a < b.
  Proof with triv.
    split. intro H.
    - inversion H...
    - constructor...
  Qed.

End defs.

Create HintDb solveSortedDB discriminated.

Create HintDb solveSortedRWs discriminated.

Hint Extern 10 (NotIn _ (_ ++ _)) =>
  eapply NotInl; autorewrite with solveSortedRWs: solveSortedDB.
Hint Extern 10 (NotIn _ (_ ++ _)) =>
  eapply NotInr; autorewrite with solveSortedRWs : solveSortedDB.
Hint Extern 10 (NotIn _ (_ :: _)) =>
  eapply NotInCons; autorewrite with solveSortedRWs : solveSortedDB.
Hint Extern 10 (NotIn _ _) => eapply NotInNil : solveSortedDB.

Hint Rewrite @redlts @redslt @ltssplit @sorted2both @rwslts
     @sorted2lts @sorted2slt @sorted2both2 @lts2lt @slt2lt : solveSortedRWs.

Hint Rewrite <- app_assoc : solveSortedRWs.
Hint Rewrite <- app_comm_cons : solveSortedRWs.

Hint Constructors LocallySorted lts slt : solveSortedDB.

Hint Resolve lts_trans slt_trans sltleft sltright ltsright1
     sltlts2sorted sltapp ltssorted sltsorted : solveSortedDB.

Hint Extern 10 (lt _ _) => eapply transitivity : solveSortedDB.

Ltac solve_sorted :=
  intros;
  subst;
  repeat (simpl in *; autorewrite with solveSortedRWs in *);
  intuition idtac;
  eauto with solveSortedDB.

(************************************************************************)

Section Examples.
  Context {A : Set}.
  Context {ordA : Ordered A}.

  Infix "<" := lt (at level 70) : list_scope.

  Goal forall p q r s t u v a b c d e f,
         sorted(p++[a]++(q++[b])++r++([c]++(s++[d])++t++[e])++(u++[f])++v) ->
         sorted(q++([c]++t)++[e]++v).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, 
         sorted ((p++q++[b])++r) -> sorted (p++[a]++q) -> a < b ->
         sorted (p++([a]++q++[b])++r).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, sorted (p++[a]++q++[b]++r) -> sorted(p++q++[b]++r).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, sorted (p++[a]++q++[b]++r) -> sorted(p++[a]++q++r).
  Proof. solve_sorted. Qed.

  Goal forall p q a b, sorted ((p++[a])++[b]++q) -> sorted(p++[a]++q).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, sorted ((p++a::q)++b::r) -> sorted (q++b::r).
  Proof. solve_sorted. Qed.

  Goal forall p q r s a b c, sorted ((p++a::(q++b::r))++c::s) ->
                             sorted (p++a::((q++b::r)++c::s)).
  Proof. solve_sorted. Qed.

  Goal forall l a, lts l a -> sorted l.
  Proof. solve_sorted. Qed.

  Goal forall l a, slt a l -> sorted l.
  Proof. solve_sorted. Qed.

End Examples.

(* Local Variables: *)
(* company-coq-local-symbols: (("++" . ?⧺) ("..." . ?…) ("!<" . ?◁) ("<!" . ?⋖) ("sorted" . ?⊿)) *)
(* End: *)
