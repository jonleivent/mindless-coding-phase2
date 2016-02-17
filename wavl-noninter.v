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

(* A non-interactive version of wavl.v, with all functions defined using ":=".
Indexless types are used to keep match expressions simple.  Note that the
leaves of all but the most trivial functions are still filled in using proof
search. *)

Require Import elist.
Require Import ezbool.
Require Import ExtrOcamlBasic.
Require Import utils.
Require Import posall.
Require Import hypiter.

Generalizable All Variables.

Context {A : Set}.

Context {ordA : Ordered A}.

Notation EL := ##(list A).

Inductive wavltree(k : EZ)(g lg rg : EB)(f : EL) : Set :=
| Missing
    (eqf : f = [])
    (eqk : k = #- #1)
    (eqlg : lg = #false)
    (eqrg : rg = #false)
| Node
    (ug : bool)
    (equg : g = #ug)
    `(eqlk : lk = k #- #1 #- Eb2Z lg)
    `(lc : wavltree lk lg llg lrg lf)
    (d : A)
    `(eqrk : rk = k #- #1 #- Eb2Z rg)
    `(rc : wavltree rk rg rlg rrg rf)
    (s : Esorted (lf ++ ^d ++ rf))
    (leaf : k = #1 -> lk = #0 \/ rk = #0)
    (eqf : f = lf ++ ^d ++ rf).

Lemma wavlkgtm1 : forall `(t : wavltree ek g lg rg f), exists k, #k = ek /\ k >= -1.
Proof.
  intros.
  induction t.
  all: bang.
Qed.

Lemma wavlkge0 : forall `(t : wavltree ek g lg rg f), f <> [] -> exists k, #k = ek /\ k >= 0.
Proof.
  intros.
  destruct t.
  all: posall @wavlkgtm1; bang.
Qed.

Lemma wavlfnenil :
  forall `(t : wavltree k g lg rg f), k <> #- #1 -> f <> [].
Proof.
  intros.
  destruct t.
  all: bang.
Qed.

Lemma clearleaf1 : forall `(t : wavltree (#- #1) g lg rg f), f= [ ] /\ lg = #false /\ rg = #false.
Proof.
  intros.
  posall @wavlkge0.
  destruct t.
  all: bang.
Qed.

Lemma clearleaf2 : forall `(t : wavltree k g lg rg []), k = #- #1 /\ lg = #false /\ rg = #false.
Proof.
  intros.
  destruct t.
  - tauto.
  - fnenil.
Qed.

Ltac bang_setup_tactic ::=
  let f H :=
      lazymatch type of H with
      | wavltree _ _ _ _ _ =>
        first [apply clearleaf1 in H
              |apply clearleaf2 in H
              |pose proof (wavlkge0 H ltac:(assumption||fnenil))
              |pose proof (wavlkgtm1 H)
              ]
      | _ => idtac
      end
  in
  hyps => loop f.

Definition isMissing`(t : wavltree ek g lg rg f)
  : {f = [] /\ lg = #false /\ rg = #false /\ exists k, #k = ek /\ k = -1} + {f <> [] /\ exists k, #k = ek /\ k >= 0} :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(left;bang)
  | Node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ltac:(right;bang)
  end.

Lemma wavls : forall `(t : wavltree k g lg rg f), Esorted f.
Proof.
  dintros.
  onhead wavltree destr.
  - unerase.
    solve_sorted.
  -  subst; assumption.
Qed.

Ltac ss_setup_tactic :=
  let f H := try apply wavls in H in
  hyps => loop f.

Ltac ss := ss_setup_tactic; unerase; solve[solve_sorted].

Inductive findResult(x : A)(f : EL) : Set :=
| Found`(eqf : f = fl ++ ^x ++ fr)
| NotFound(ni : ENotIn x f).

Ltac solve_find :=
  dintros;
  reassoc;
  solve[eapply Found; reflexivity | eapply NotFound; ss].

Fixpoint find(x : A)`(t : wavltree k g lg rg f) : findResult x f :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_find)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match (compare_spec x d) with
    | CompEqT _ _ _ => ltac:(solve_find)
    | CompLtT _ _ _ =>
      match (find x lc) with
      | Found _ _ _ => ltac:(solve_find)
      | NotFound _ _ _ => ltac:(solve_find)
      end
    | CompGtT _ _ _ =>
      match (find x rc) with
      | Found _ _ _ => ltac:(solve_find)
      | NotFound _ _ _ => ltac:(solve_find)
      end
    end
  end.

Ltac wavl_missing :=
  eapply Missing; [reflexivity|boom..].

Definition setgap`(t : wavltree k ig lg rg f)(g : bool) : wavltree k #g lg rg f :=
  match t with
  | Missing _ _ _ _ _ eqf eqk eqlg eqrg =>
    Missing _ _ _ _ _ eqf eqk eqlg eqrg
  | Node _ _ _ _ _ _ _ eqlk lc d eqrk rc s leaf eqf =>
    Node _ _ _ _ _ g eq_refl eqlk lc d eqrk rc s leaf eqf
  end.

Definition getgap`(t : wavltree k eg lg rg f) : {g | f <> [] -> #g = eg} :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(exists false; boom)
  | Node _ _ _ _ _ ug _ _ _ _ _ _ _ _ _ => ltac:(exists ug; boom)
  end.

Definition gofis`(t : wavltree k eg lg rg f)(g : bool) : {k <> #- #1 /\ #g = eg} + {k = #- #1 \/ #g <> eg} :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(right; boom)
  | Node _ _ _ _ _ ug _ _ _ _ _ _ _ _ _ =>
    if (Bool.bool_dec g ug)
    then ltac:(left; boom)
    else ltac:(right; boom)
  end.

Ltac wavl_assumption :=
  (idtac + eapply setgap);
  multimatch goal with
    H : wavltree _ _ _ _ ?F |- wavltree _ _ _ _ ?F' =>
    replace F' with F by (rewrite ?Eapp_assoc; reflexivity);
    force exact H;
    [boom..]
  end.

Ltac solve_wavl :=
  dintros;
  (wavl_missing + wavl_assumption + wavl_construction)
with wavl_construction :=
  reassoc;
  eapply Node;
  [..|reflexivity];
  [boom
  |boom
  |solve_wavl
  |boom
  |solve_wavl
  |ss
  |boom
  ].

Definition rot1
           `(lt : wavltree k #false llg lrg lf)
           (x : A)
           `(rt : wavltree (k #- #2) #true rlg rrg rf)
           (gne : llg <> lrg)
           (s : Esorted (lf ++ ^x ++ rf))
  : forall g, wavltree k #g #false #false (lf ++ ^x ++ rf) :=
  match lt with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(bang)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match rc with
    | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_wavl)
    | Node _ _ _ _ _ rg _ _ _ _ _ _ _ _ _ =>
      if (Bool.Sumbool.sumbool_of_bool rg)
      then ltac:(solve_wavl)
      else ltac:(solve_wavl)
    end
  end.

Definition rot2
           `(lt : wavltree (k #- #2) #true llg lrg lf)
           (x : A)
           `(rt : wavltree k #false rlg rrg rf)
           (gne : rlg <> rrg)
           (s : Esorted (lf ++ ^x ++ rf))
  : forall g, wavltree k #g #false #false (lf ++ ^x ++ rf) :=
  match rt with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(bang)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match lc with
    | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_wavl)
    | Node _ _ _ _ _ lg _ _ _ _ _ _ _ _ _ =>
      if (Bool.Sumbool.sumbool_of_bool lg)
      then ltac:(solve_wavl)
      else ltac:(solve_wavl)
    end
  end.

Ltac use_rot :=
  reassoc;
  (eapply rot1 + eapply rot2);
  [wavl_assumption
  |wavl_assumption
  |boom
  |ss
  ].

Inductive insertedHow(ki ko : EZ)(gi go lgo rgo : EB)(f : EL) : Set :=
| ISameK(_: ko = ki)(_: f <> [])(_: go = gi)
| IWasMissing(_: ki= #- #1)(_: ko = #0)(_: f = [])(_: go = #false)
| IHigherK(_: ko=ki #+ #1)(_: lgo <> rgo)(_: f <> [])(_: go = #false).

Inductive insertResult(x: A)(k : EZ)(g lg rg : EB)(f : EL) : Set :=
| FoundByInsert`(eqf : f=fl ++ ^x ++ fr)
| Inserted`(eqf : f = fl ++ fr)
          `(t : wavltree ko go lgo rgo (fl ++ ^x ++ fr))
          (i : insertedHow k ko g go lgo rgo f).

Ltac solve_wavl2 := use_rot + solve_wavl.

Ltac solve_insert :=
  dintros;
  (idtac + change ([]:EL) with ([] ++ []:EL));
  reassoc;
  ((eapply FoundByInsert; reflexivity) +
   (eapply Inserted;
     [reflexivity|solve_wavl2|econstructor;[solve[fnenil|boom]..]])).

Fixpoint insert(x : A)`(t : wavltree k g lg rg f) : insertResult x k g lg rg f :=
match t with
| Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_insert)
| Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
  match (compare_spec x d) with
  | CompEqT _ _ _ => ltac:(solve_insert)
  | CompLtT _ _ _ =>
    match (insert x lc) with
    | FoundByInsert _ _ _ _ _ _ _ => ltac:(solve_insert)
    | Inserted _ _ _ _ _ _ _ _ i =>
      match i with
      | ISameK _ _ _ _ _ _ _ _ _ _ => ltac:(solve_insert)
      | IWasMissing _ _ _ _ _ _ _ _ _ _ _ =>
        if (isMissing rc)
        then ltac:(solve_insert)
        else ltac:(solve_insert)
      | IHigherK _ _ _ _ _ _ _ _ _ _ _ =>
        if (gofis lc true)
        then ltac:(solve_insert)
        else if (gofis rc false)
             then ltac:(solve_insert)
             else ltac:(solve_insert)
      end
    end
  | CompGtT _ _ _ =>
    match (insert x rc) with
    | FoundByInsert _ _ _ _ _ _ _ => ltac:(solve_insert)
    | Inserted _ _ _ _ _ _ _ _ i =>
      match i with
      | ISameK _ _ _ _ _ _ _ _ _ _ => ltac:(solve_insert)
      | IWasMissing _ _ _ _ _ _ _ _ _ _ _ =>
        if (isMissing lc)
        then ltac:(solve_insert)
        else ltac:(solve_insert)
      | IHigherK _ _ _ _ _ _ _ _ _ _ _ =>
        if (gofis rc true)
        then ltac:(solve_insert)
        else if (gofis lc false)
             then ltac:(solve_insert)
             else ltac:(solve_insert)
      end
    end
  end
end.

(**********************************************************************)

Inductive tryLoweringResult`(t : wavltree k g lg rg f) : Set :=
| TLtooLow(p : lg = #false \/ rg = #false)
| TLlowered(p: lg = #true /\ rg = #true)(t': wavltree (k #- #1) g #false #false f).

Ltac solve_tl :=
  dintros;
  ((eapply TLtooLow; boom) +
   (eapply TLlowered; [boom|solve_wavl])).

Definition tryLowering`(t : wavltree k g lg rg f) : tryLoweringResult t :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_tl)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    if (gofis lc true)
    then if (gofis rc true)
         then ltac:(solve_tl)
         else ltac:(solve_tl)
    else ltac:(solve_tl)
  end.

Inductive deletedHow(ki ko : EZ)(gi go : EB) : Set :=
| DSameK(keq : ko = ki)(eg : go = gi)
| DLowerK(keq :  ki = ko #+ #1)(eg: go = #true).

Inductive delpair(k : EZ)(g : EB)(f : EL) : Set :=
| Delout`(t : wavltree ko go lgo rgo f)(d : deletedHow k ko g go).

Ltac solve_delpair :=
  dintros;
  eapply Delout;
  [|constructor;[boom..]];
  solve_wavl.

Definition drot1
           `(t : wavltree (k #- #3) #true lgo rgo f)
           (d : A)
           `(t2 : wavltree (k #- #1) #false rlg rrg rf)
           (s : Esorted (f ++ ^ d ++ rf))
           (tltl : rlg = #false \/ rrg = #false)
  : forall ug, delpair k #ug (f ++ ^d ++ rf) :=
  match t2 with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(bang)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match lc with
    | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_delpair)
    | Node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      if (gofis rc false)
      then ltac:(solve_delpair)
      else ltac:(solve_delpair)
    end
  end.

Definition drot2
           `(t2 : wavltree (k #- #1) #false llg lrg lf)
           (d : A)
           `(t : wavltree (k #- #3) #true lgo rgo f)
           (s : Esorted (lf ++ ^ d ++ f))
           (tltl : llg = #false \/ lrg = #false)
  : forall ug, delpair k #ug (lf ++ ^d ++ f) :=
  match t2 with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(bang)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match rc with
    | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_delpair)
    | Node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      if (gofis lc false)
      then ltac:(solve_delpair)
      else ltac:(solve_delpair)
    end
  end.

Ltac use_drot :=
  dintros;
  reassoc;
  (eapply drot1 + eapply drot2);
  [wavl_assumption|wavl_assumption|ss|assumption].

Ltac solve_delpair2 := use_drot + solve_delpair.

Inductive delminResult(k : EZ)(g : EB)(f : EL) : Set :=
| NoMin(eqf : f = [])
| MinDeleted(min : A)`(eqf : f = ^min ++ rf)(dr : delpair k g rf).

Ltac solve_delmin :=
  dintros;
  reassoc;
  try rewrite Eapp_nil_l;
  ((eapply NoMin; reflexivity) +
   (eapply MinDeleted; [reflexivity|solve_delpair2])).

Ltac unerase_gaps :=
  let f H :=
      try
        lazymatch type of H with
          wavltree _ ?G _ _ _ =>
          is_var G;
          case (getgap H);
          let X:=fresh in
          let G':=fresh in
          intros G' X;
          first [specialize (X ltac:(assumption||fnenil))
                |specialize (X (wavlfnenil H ltac:(bang)))];
          rewrite <-X in *;
          clear X G;
          rename G' into G
        end in
    hyps => loop f.

Fixpoint delmin`(t : wavltree k g lg rg f) : delminResult k g f :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_delmin)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match (delmin lc) with
    | NoMin _ _ _ _ => ltac:(solve_delmin)
    | MinDeleted _ _ _ _ _ (Delout _ _ _ _ (DSameK _ _ _ _ _ _)) => ltac:(solve_delmin)
    | MinDeleted _ _ _ _ _ (Delout _ _ _ _ (DLowerK _ _ _ _ _ _)) =>
      if (gofis rc false)
      then if (gofis lc true)
           then match (tryLowering rc) with
                | TLtooLow _ _ => ltac:(solve_delmin)
                | TLlowered _ _ _ => ltac:(solve_delmin)
                end
           else ltac:(solve_delmin)
      else ltac:(unerase_gaps; solve_delmin)
    end
  end.

Inductive delmaxResult(k : EZ)(g : EB)(f : EL) : Set :=
| NoMax(eqf : f = [])
| MaxDeleted(max : A)`(eqf : f = lf ++ ^max)(dr : delpair k g lf).

Ltac solve_delmax :=
  dintros;
  reassoc;
  try rewrite Eapp_nil_r;
  ((eapply NoMax; reflexivity) +
   (eapply MaxDeleted; [reflexivity|solve_delpair2])).

Fixpoint delmax`(t : wavltree k g lg rg f) : delmaxResult k g f :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_delmax)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match (delmax rc) with
    | NoMax _ _ _ _ => ltac:(solve_delmax)
    | MaxDeleted _ _ _ _ _ (Delout _ _ _ _ (DSameK _ _ _ _ _ _)) => ltac:(solve_delmax)
    | MaxDeleted _ _ _ _ _ (Delout _ _ _ _ (DLowerK _ _ _ _ _ _)) =>
      if (gofis lc false)
      then if (gofis rc true)
           then match (tryLowering lc) with
                | TLtooLow _ _ => ltac:(solve_delmax)
                | TLlowered _ _ _ => ltac:(solve_delmax)
                end
           else ltac:(solve_delmax)
      else ltac:(unerase_gaps; solve_delmax)
    end
  end.

Inductive deleteResult(x : A)(k : EZ)(g : EB)(f : EL) : Set :=
| Deleted`(eqf : f = f1 ++ ^x ++ f2)(dr : delpair k g (f1 ++ f2))
| DNotFound(ni : ENotIn x f).

Ltac solve_delete :=
  dintros;
  reassoc;
  ((eapply Deleted;[reflexivity|];
   (idtac + (rewrite Eapp_nil_r || rewrite Eapp_nil_l));
   solve_delpair2)
   + (eapply DNotFound; ss)).

Fixpoint delete(x : A)`(t : wavltree k g lg rg f) : deleteResult x k g f :=
  match t with
  | Missing _ _ _ _ _ _ _ _ _ => ltac:(solve_delete)
  | Node _ _ _ _ _ _ _ _ lc d _ rc _ _ _ =>
    match (compare_spec x d) with
    | CompEqT _ _ _ =>
      if (gofis rc false)
      then match (delmin rc) with
           | NoMin _ _ _ _ => ltac:(solve_delete)
           | MinDeleted _ _ _ _ _ (Delout _ _ _ _ (DSameK _ _ _ _ _ _)) => ltac:(solve_delete)
           | MinDeleted _ _ _ _ _ (Delout _ _ _ _ (DLowerK _ _ _ _ _ _)) =>
             if (isMissing lc)
             then ltac:(solve_delete)
             else ltac:(solve_delete)
           end
      else match (delmax lc) with
           | NoMax _ _ _ _ => ltac:(solve_delete)
           | MaxDeleted _ _ _ _ _ (Delout _ _ _ _ (DSameK _ _ _ _ _ _)) => ltac:(solve_delete)
           | MaxDeleted _ _ _ _ _ (Delout _ _ _ _ (DLowerK _ _ _ _ _ _)) => ltac:(unerase_gaps; solve_delete)
           end
    | CompLtT _ _ _ =>
      match (delete x lc) with
      | Deleted _ _ _ _ _ (Delout _ _ _ _ (DSameK _ _ _ _ _ _)) => ltac:(solve_delete)
      | Deleted _ _ _ _ _ (Delout _ _ _ _ (DLowerK _ _ _ _ _ _)) =>
          if (gofis lc true)
          then if (gofis rc true)
               then ltac:(solve_delete)
               else if (tryLowering rc)
                    then ltac:(solve_delete)
                    else ltac:(solve_delete)
          else if (isMissing rc)
               then ltac:(solve_delete)
               else ltac:(solve_delete)
      | DNotFound _ _ _ _ _ => ltac:(solve_delete)
      end
    | CompGtT _ _ _ =>
      match (delete x rc) with
      | Deleted _ _ _ _ _ (Delout _ _ _ _ (DSameK _ _ _ _ _ _)) => ltac:(solve_delete)
      | Deleted _ _ _ _ _ (Delout _ _ _ _ (DLowerK _ _ _ _ _ _)) =>
          if (gofis rc true)
          then if (gofis lc true)
               then ltac:(solve_delete)
               else if (tryLowering lc)
                    then ltac:(solve_delete)
                    else ltac:(solve_delete)
          else if (isMissing lc)
               then ltac:(solve_delete)
               else ltac:(solve_delete)
      | DNotFound _ _ _ _ _ => ltac:(solve_delete)
      end
    end
  end.

(* End Wavltree. *)

Set Printing Width 120.

Extract Inductive delpair => "( * )" [ "" ].

Extraction Inline negb.
Extraction Inline Bool.bool_dec.
Extraction Inline Bool.Sumbool.sumbool_of_bool.
Extraction Inline EqdepFacts.internal_eq_rew_r_dep.

Extraction "wavl-noninter.ml" find insert delete.
