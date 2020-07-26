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

Require Export Coq.Classes.RelationClasses.

Set Default Goal Selector "all".

Class Ordered(A : Set) :=
  { lt : A -> A -> Prop;
    lt_strict :> StrictOrder lt
  }.

Class OrderedKeyed (A K : Set) :=
  { keyof : A -> K;
    OA :> Ordered A
  }.

Class KeyOrdered (A K : Set) :=
  { getkey : A -> K;
    OK :> Ordered K
  }.

Definition KOlt{A K : Set}`{KeyOrdered A K}(a b : A) : Prop := lt (getkey a) (getkey b).

Instance KOisO A K `{KeyOrdered A K} : Ordered A.
Proof.
  destruct (_:KeyOrdered A K) as [gk [ltk [SOI SOT]]]. unshelve eexists.
  - intros a b. exact (ltk (gk a) (gk b)).
  - split.
    + unfold Irreflexive, Reflexive, complement in *. intro. apply SOI.
    + unfold Transitive in *. intros x y z. apply SOT.
Defined.

Instance KOisOK A K `{KeyOrdered A K} : OrderedKeyed A K :=
  { keyof := getkey }.

Class ComparableKeyed (A K : Set) :=
  { OKOK :> OrderedKeyed A K;
    compare : K -> K -> comparison;
    compare_spec x y: CompareSpecT (eq x y)
                                   (forall (a b : A), x = keyof a -> y = keyof b -> lt a b)
                                   (forall (a b : A), x = keyof a -> y = keyof b -> lt b a)
                                   (compare x y);
    lt_same_keys w x y z: lt w y -> keyof x = keyof w -> keyof z = keyof y -> lt x z
  }.

Require Coq.Init.Nat.
Require Coq.Arith.PeanoNat.

Module Test.

  Import Nat.
  Import PeanoNat.
  
  Open Scope nat_scope.

  Context {A : Set}.
  Context {Ord : Ordered A}.

  Record OK : Set := { val : A; key : nat }.

  Definition OKlt (a b : OK) : Prop := a.(key) < b.(key).

  Lemma le_Sn_n : forall n, S n <= n -> False.
  Proof.
    induction n as [|? IHn]. intro H.
    - inversion H.
    - apply IHn. apply le_S_n. assumption.
  Qed.

  Lemma OKlt_strict : StrictOrder OKlt.
  Proof.
    eexists. red.
    - red. red. intros [v k]. cbv. apply le_Sn_n.
    - intros [? ?] [? ykey] [? ?]. unfold OKlt, key. transitivity ykey. assumption.
  Qed.

  Instance OKOrd : Ordered OK := { lt := OKlt; lt_strict := OKlt_strict }.

  Lemma OKOrd_compare_spec (x y:nat) :
    CompareSpecT (eq x y)
                 (forall (a b : OK), x = a.(key) -> y = b.(key) -> OKlt a b)
                 (forall (a b : OK), x = a.(key) -> y = b.(key) -> OKlt b a)
                 (Nat.compare x y).
  Proof.
    destruct (CompareSpec2Type (Nat.compare_spec x y)). constructor.
    - assumption.
    - intros ? ? -> -> . assumption.
    - intros ? ? -> -> . assumption.
  Qed.

  Lemma OKOrd_lt_same_keys w x y z :
    OKlt w y -> x.(key) = w.(key) -> z.(key) = y.(key) -> OKlt x z.
  Proof.
    unfold OKlt. intros H -> -> . assumption.
  Qed.

  Instance OKnat : OrderedKeyed OK nat := { keyof := key }.
 
  Instance CKnat : ComparableKeyed OK nat :=
    { compare := Nat.compare;
      compare_spec := OKOrd_compare_spec;
      lt_same_keys := OKOrd_lt_same_keys
    }.

End Test.

