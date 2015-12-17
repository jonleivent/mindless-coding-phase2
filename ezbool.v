(***********************************************************************

Copyright (c) 2015 Jonathan Leivent

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

Require Export erasable.
Import ErasableNotation.
Require Export ZArith.
Require Import utils.
Require Import posall.
Require Import factorevars.
Require Import hypiter.

Notation EZ := ##Z.

Open Scope Z_scope.

Arguments Z.add x y : simpl nomatch.
Arguments Z.sub m n : simpl nomatch.
Arguments Z.opp x : simpl nomatch.
Arguments Z.mul x y : simpl nomatch.

Definition ezadd(x y : EZ) := (lift2 Z.add) x y.
Arguments ezadd !x !y.
Definition ezsub(x y : EZ) := (lift2 Z.sub) x y.
Arguments ezsub !x !y.
Definition ezopp(x : EZ) := (lift1 Z.opp) x.
Arguments ezopp !x.
Definition ezmul(x y : EZ) := (lift2 Z.mul) x y.
Arguments ezmul !x !y.

Notation "x #+ y" := (ezadd x y)
                       (at level 50, left associativity).
Notation "x #- y" := (ezsub x y)
                       (at level 50, left associativity).
Notation "#- x" := (ezopp x)
                     (at level 35, right associativity).
Notation "x #* y" := (ezmul x y)
                       (at level 40, left associativity).

Opaque Z.mul.

Notation EB := ##bool.

Definition Enegb := lift1 negb.

Definition b2Z(b : bool) : Z := if b then 1 else 0.
Definition Eb2Z := lift1 b2Z.

Lemma b2Zbounds : forall b, b2Z b >= 0 /\ b2Z b <= 1.
Proof.
  dintros.
  destruct b; cbn; omega.
Qed.

Ltac destruct_goal_bool :=
  match goal with
  | B : bool |- context[?G] => constr_eq B G; destruct B
  end.

(* How should we classify rewrite rules?  By their applicability -
meaning by the type of formula in which they would have a chance of
rewriting something. *)

Set Default Proof Using "Type".

Section Bool_Rewrites.

  Variables b b1 b2 : bool.

  Tactic Notation "!!" :=
    repeat destruct_goal_bool; cbn; intuition congruence.

  (*bool term rewrites*)
  Lemma negbf_rw : negb false = true.  Proof. !!.  Qed.
  Lemma negbt_rw : negb true = false. Proof. !!. Qed.
  Lemma dubnegb_rw : negb (negb b) = b. Proof. !!. Qed.

  (*bool equality rewrites*)
  Lemma teqt_rw : true = true <-> True. Proof. !!. Qed.
  Lemma feqf_rw : false = false <-> True. Proof. !!. Qed.
  Lemma teqf_rw : true = false <-> False. Proof. !!. Qed.
  Lemma feqt_rw : false = true <-> False. Proof. !!. Qed.
  Lemma bneq_rw : b1 <> b2 <-> b1 = negb b2. Proof. !!. Qed.
  Lemma negbfl_rw : negb b = false <-> b = true. Proof. !!. Qed.
  Lemma negbfr_rw : false = negb b <-> b = true. Proof. !!. Qed.
  Lemma negbtl_rw : negb b = true <-> b = false. Proof. !!. Qed.
  Lemma negbtr_rw : true = negb b <-> b = false. Proof. !!. Qed.
  Lemma negb_inj_rw : negb b1 = negb b2 <-> b1 = b2. Proof. !!. Qed.

End Bool_Rewrites.

Hint Rewrite
     negbf_rw negbt_rw dubnegb_rw
  : bool_term_rws simp_rws term_rws.

Hint Rewrite
     teqt_rw feqf_rw teqf_rw feqt_rw bneq_rw negbfl_rw negbfr_rw negbtl_rw
     negbtr_rw negb_inj_rw
  : bool_eq_rws simp_rws eq_rws.

Section EB_Rewrites.
  Variables b b1 b2 : EB.

  Tactic Notation "!!" :=
    unerase; cbn; autorewrite with bool_term_rws bool_eq_rws unerase_rws; tauto.

  (*EB term rewrites*)
  Lemma Enegbf_rw : Enegb #false = #true. Proof. !!. Qed.
  Lemma Enegbt_rw : Enegb #true = #false. Proof. !!. Qed.
  Lemma Edubnegb_rw : Enegb (Enegb b) = b. Proof. !!. Qed.

  (*EB equality rewrites*)
  Lemma Eteqt_rw : #true = #true <-> True. Proof. !!. Qed.
  Lemma Efeqf_rw : #false = #false <-> True. Proof. !!. Qed.
  Lemma Eteqf_rw : #true = #false <-> False. Proof. !!. Qed.
  Lemma Efeqt_rw : #false = #true <-> False. Proof. !!. Qed.
  Lemma Ebneq_rw : b1 <> b2 <-> b1 = Enegb b2. Proof. !!. Qed.
  Lemma Enegbfl_rw : Enegb b = #false <-> b = #true. Proof. !!. Qed.
  Lemma Enegbfr_rw : #false = Enegb b <-> b = #true. Proof. !!. Qed.
  Lemma Enegbtl_rw : Enegb b = #true <-> b = #false. Proof. !!. Qed.
  Lemma Enegbtr_rw : #true = Enegb b <-> b = #false. Proof. !!. Qed.
  Lemma Enegb_inj_rw : Enegb b1 = Enegb b2 <-> b1 = b2. Proof. !!. Qed.
  
End EB_Rewrites.

Hint Rewrite
     Enegbf_rw Enegbtr_rw Edubnegb_rw
  : EB_term_rws simp_rws term_rws.

Hint Rewrite
     Eteqt_rw Efeqf_rw Eteqf_rw Efeqt_rw Ebneq_rw Enegbfl_rw Enegbfr_rw
     Enegbtl_rw Enegbtr_rw Enegb_inj_rw
  : EB_eq_rws eq_rws.

Section EZ_Desharping_Rewrites.
  Variables m n : Z.
  Variable b : bool.

  Tactic Notation "!!" := cbn; reflexivity.

  Lemma eadd_desharp_rw : (#n #+ #m) = #(n + m). Proof. !!. Qed.
  Lemma esub_desharp_rw : (#n #- #m) = #(n - m). Proof. !!. Qed.
  Lemma emul_desharp_rw : (#n #* #m) = #(n * m). Proof. !!. Qed.
  Lemma eopp_desharp_rw : #- #n = #(- n). Proof. !!. Qed.
  Lemma Enegb_desharp_rw : Enegb #b = #(negb b). Proof. !!. Qed.
  Lemma Eb2Z_desharp_rw : Eb2Z #b = #(b2Z b). Proof. !!. Qed.

End EZ_Desharping_Rewrites.

Hint Rewrite
     eadd_desharp_rw esub_desharp_rw emul_desharp_rw eopp_desharp_rw
     Enegb_desharp_rw Eb2Z_desharp_rw
  : desharping_rws unerase_rws.

Hint Rewrite <-
     eadd_desharp_rw esub_desharp_rw emul_desharp_rw eopp_desharp_rw
     Enegb_desharp_rw Eb2Z_desharp_rw
  : ensharping_rws simp_rws.

Section B2Z_Rewrites.
  Variable b b1 b2 : bool.

  Tactic Notation "!!" :=
    repeat destruct_goal_bool; cbn; intuition congruence.

  (*b2Z term rewrites*)
  Lemma b2Zt_rw : b2Z true = 1. Proof. !!. Qed.
  Lemma b2Zf_rw : b2Z false = 0. Proof. !!. Qed.
  Lemma b2Z_negb_rw : b2Z (negb b) = 1 - b2Z b. Proof. !!. Qed.

  (*b2Z equality rewrites*)
  Lemma b2Z_inj_rw : b2Z b1 = b2Z b2 <-> b1 = b2. Proof. !!. Qed.
  Lemma b2Zeq1l_rw : b2Z b = 1 <-> b = true. Proof. !!. Qed.
  Lemma b2Zeq1r_rw : 1 = b2Z b <-> b = true. Proof. !!. Qed.
  Lemma b2Zeq0l_rw : b2Z b = 0 <-> b = false. Proof. !!. Qed.
  Lemma b2Zeq0r_rw : 0 = b2Z b <-> b = false. Proof. !!. Qed.
  Lemma b2Zeq1mb2Z_rw : b2Z b1 = 1 - b2Z b2 <-> b1 = negb b2. Proof. !!. Qed.
  Lemma b2Zeq1mb2Zs_rw : 1 - b2Z b2 = b2Z b1 <-> b1 = negb b2. Proof. !!. Qed.
  Lemma b2Zeqnb2Zp1_rw : b2Z b1 = - b2Z b2 + 1 <-> b1 = negb b2. Proof. !!. Qed.
  Lemma b2Zeqnb2Zp1s_rw : - b2Z b2 + 1 = b2Z b1 <-> b1 = negb b2. Proof. !!. Qed.

End B2Z_Rewrites.

Hint Rewrite
     b2Zt_rw b2Zf_rw b2Z_negb_rw
  : b2Z_term_rws simp_rws term_rws bang_rws.

Hint Rewrite
     b2Z_inj_rw b2Zeq1l_rw b2Zeq1r_rw b2Zeq0l_rw b2Zeq0r_rw
     b2Zeq1mb2Z_rw b2Zeq1mb2Zs_rw b2Zeqnb2Zp1_rw b2Zeqnb2Zp1s_rw
  : b2Z_eq_rws eq_rws.

Hint Rewrite <- b2Z_inj_rw : simp_rws.

Section Eb2Z_Rewrites.
  Variables b b1 b2 : EB.

  Tactic Notation "!!" :=
    unerase; autorewrite with b2Z_term_rws b2Z_eq_rws; tauto.

  (*Eb2Z term rewrites*)
  Lemma Eb2Zt_rw : Eb2Z #true = #1. Proof. !!. Qed.
  Lemma Eb2Zf_rw : Eb2Z #false = #0. Proof. !!. Qed.
  Lemma Eb2Z_negb_rw : Eb2Z (Enegb b) = #1 #- Eb2Z b. Proof. !!. Qed.

  (*Eb2Z equality rewrites*)
  Lemma Eb2Z_inj_rw : Eb2Z b1 = Eb2Z b2 <-> b1 = b2. Proof. !!. Qed.
  Lemma Eb2Zeq1l_rw : Eb2Z b = #1 <-> b = #true. Proof. !!. Qed.
  Lemma Eb2Zeq1r_rw : #1 = Eb2Z b <-> b = #true. Proof. !!. Qed.
  Lemma Eb2Zeq0l_rw : Eb2Z b = #0 <-> b = #false. Proof. !!. Qed.
  Lemma Eb2Zeq0r_rw : #0 = Eb2Z b <-> b = #false. Proof. !!. Qed.
  Lemma Eb2Zeq1mb2Z_rw : Eb2Z b1 = #1 #- Eb2Z b2 <-> b1 = Enegb b2. Proof. !!. Qed.
  Lemma Eb2Zeq1mb2Zs_rw : #1 #- Eb2Z b2 = Eb2Z b1 <-> b1 = Enegb b2. Proof. !!. Qed.
  Lemma Eb2Zeqnb2Zp1_rw :
    Eb2Z b1 = #- Eb2Z b2 #+ #1 <-> b1 = Enegb b2. Proof. !!. Qed.
  Lemma Eb2Zeqnb2Zp1s_rw :
    #- Eb2Z b2 #+ #1 = Eb2Z b1 <-> b1 = Enegb b2. Proof. !!. Qed.

End Eb2Z_Rewrites.

Hint Rewrite Eb2Zt_rw Eb2Zf_rw Eb2Z_negb_rw
  : Eb2Z_term_rws simp_rws term_rws.

Hint Rewrite
     Eb2Z_inj_rw Eb2Zeq1l_rw Eb2Zeq1r_rw Eb2Zeq0l_rw Eb2Zeq0r_rw
     Eb2Zeq1mb2Z_rw Eb2Zeq1mb2Zs_rw Eb2Zeqnb2Zp1_rw Eb2Zeqnb2Zp1s_rw
  : Eb2Z_eq_rws eq_rws.

Hint Rewrite <- Eb2Z_inj_rw : simp_rws.

Section Z_LHSify_Rewrites.
  Variables x y z : Z.

  Tactic Notation "!!" := omega.

  Lemma zlhs_rw : x = y <-> x - y = 0. Proof. !!. Qed.
  Lemma zadd1_lhs_rw : x + y = z <-> x = z - y. Proof. !!. Qed.
  Lemma zadd2_lhs_rw : x + y = z <-> y = z - x. Proof. !!. Qed.
  Lemma zsub1_lhs_rw : x - y = z <-> x = z + y. Proof. !!. Qed.
  Lemma zsub2_lhs_rw : x - y = z <-> y = x - z. Proof. !!. Qed.
  Lemma zopp_lhs_rw : -x = y <-> x = -y. Proof. !!. Qed.

  Lemma ziso1_rw : y = 0 <-> x = x + y. Proof. !!. Qed.
  Lemma ziso2_rw : y = 0 <-> x = x - y. Proof. !!. Qed.

End Z_LHSify_Rewrites.


Section EZ_LHSify_Rewrites.
  Variables x y z : EZ.

  Tactic Notation "!!" := unerase; omega.

  Lemma Ezlhs_rw : x = y <-> x #- y = #0. Proof. !!. Qed.
  Lemma Ezadd1_lhs_rw : x #+ y = z <-> x = z #- y. Proof. !!. Qed.
  Lemma Ezadd2_lhs_rw : x #+ y = z <-> y = z #- x. Proof. !!. Qed.
  Lemma Ezsub1_lhs_rw : x #- y = z <-> x = z #+ y. Proof. !!. Qed.
  Lemma Ezsub2_lhs_rw : x #- y = z <-> y = x #- z. Proof. !!. Qed.
  Lemma Ezopp_lhs_rw : #- x = y <-> x = #- y. Proof. !!. Qed.

  Lemma Eziso1_rw : y = #0 <-> x = x #+ y. Proof. !!. Qed.
  Lemma Eziso2_rw : y = #0 <-> x = x #- y. Proof. !!. Qed.

End EZ_LHSify_Rewrites.

Lemma ezring_theory : 
  ring_theory (R:=EZ) #0 #1 ezadd ezmul ezsub ezopp eq.
Proof.
  constructor.
  all: intros; unerase; ring.
Qed.

Ltac ezconst term :=
  match term with
  | # ?x => Zcst x
  | _ => InitialRing.NotConstant
  end.

Ltac EZring_preprocess :=
  autorewrite with term_rws;
  autorewrite with ensharping_rws.

Ltac EZring_postprocess :=
  idtac.

Add Ring ezring : 
  ezring_theory (abstract,
                 constants [ezconst],
                 preprocess [EZring_preprocess],
                 postprocess [EZring_postprocess]
                ).

Ltac safe_ring_simplify_in H :=
  factor_evars H;
  try ring_simplify in H;
  defactor_all_evars.

Ltac safe_ring_simplify :=
  factor_conc_evars;
  try ring_simplify;
  defactor_all_evars.

Ltac rsimp_term T :=
  lazymatch T with
  | ?F ?A => rsimp_fun F A
  | ?A -> ?C => rsimp_term A; rsimp_term C
  | _ => idtac
  end
with rsimp_fun F A :=
  let T:=constr:(F A) in
  let tT:=type of T in
  tryif first [constr_eq tT Z|constr_eq tT (EZ)]
  then let e:=fresh in
       let ee:=fresh in
       remember T as e eqn:ee in *;
       safe_ring_simplify_in ee;
       (*do not use subst e - it causes problems*)
       rewrite ?ee in *; clear e ee
  else (rsimp_term F; rsimp_term A).

Ltac rsimp_in H :=
  let T:=type of H in rsimp_term T.

Ltac rsimp_goal :=
  lazymatch goal with
  | |- ?G => rsimp_term G
  end.

Ltac rsimp :=
  rsimp_goal;
  hyps => loop rsimp_in.

(************************************************************************)

Hint Rewrite <- b2Z_inj_rw : bang_rws.

Ltac bang_setup_tactic := idtac. (*to be redefined*)

Ltac bang :=
  dintros;
  unsetall;
  try tauto;
  first[check_in_prop|exfalso];
  bang_setup_tactic;
  unerase;
  autorewrite with bang_rws in *;
  posall b2Zbounds;
  (omega ||
   lazymatch goal with
   | |- _ /\ _ => deconj; first[congruence|omega]
   | _ => congruence
   end).

Ltac check_cycle V Sub :=
  lazymatch Sub with context[V] => fail | _ => idtac end.

Ltac notin_conc_rhs E :=
  lazymatch goal with
  | |- _ = ?R => check_cycle E R
  | |- ?G => fail 99 "notin_conc_rhs when conc is " G
  end.

(* TBD: can we speed up the inst funs by using a bool xor fun to
combine b/negb b by delaying the sign?
*)

Ltac inst_bool E :=
  ((instantiate (1:=true) in (Value of E)) +
   (instantiate (1:=false) in (Value of E)) +
   (multimatch goal with
     | b : bool |- _ =>
       (instantiate (1:=b) in (Value of E)) +
       (instantiate (1:=negb b) in (Value of E))
     end));
  unfold E in *; clear E;
  autorewrite with simp_rws in *.

Ltac inst_EB E :=
  ((instantiate (1:=#true) in (Value of E)) +
   (instantiate (1:=#false) in (Value of E)) +
   (multimatch goal with
     | b : EB |- _ =>
       (instantiate (1:=b) in (Value of E)) +
       (instantiate (1:=Enegb b) in (Value of E))
     | b : bool |- _ =>
       (instantiate (1:=#b) in (Value of E)) +
       (instantiate (1:=Enegb #b) in (Value of E))
     end));
  unfold E in *; clear E;
  autorewrite with simp_rws in *.

Ltac unify_EBeq E Ealone :=
  rewrite Ezlhs_rw;
  first [rewrite (Eziso1_rw (Eb2Z E));
          ring_simplify; notin_conc_rhs Ealone
        |rewrite (Eziso2_rw (Eb2Z E));
          ring_simplify; notin_conc_rhs Ealone];
  autorewrite with Eb2Z_eq_rws;
  defactor_all_evars;
  reflexivity.

Ltac unify_EZeq E Ealone :=
  rewrite Ezlhs_rw;
  first[rewrite (Eziso1_rw E);
         ring_simplify; notin_conc_rhs Ealone
       |rewrite (Eziso2_rw E);
         ring_simplify; notin_conc_rhs Ealone];
  defactor_all_evars;
  reflexivity.

Ltac boom :=
  dintros;
  defactor_all_evars;
  lazymatch goal with
    |- ?G =>
    tryif has_evar G then solve_EBeq else bang
  end
with solve_EBeq :=
  first
    [ simple_reflex
    | factor_conc_evars;
      match goal with
      | [E := ?V : Z |- (@eq EZ _ _)] =>
        (*We should never see a Z equality - only EZs - because we
        don't call unerase until bang, and no Zs appear without
        erasure as args of funs/ctors.  If this changes, as it would
        if we were developing a structure that, unlike wavltree, had Z
        args, then we will need to revisit this. *)
        is_evar V; (*unify_EZeq (#E) E*) fail 999 "solve_EBeq found a Z evar" V
      | [E := ?V : EZ |- (@eq EZ _ _)] =>
        is_evar V; unify_EZeq E E
      | [E := ?V : EB |- (@eq EZ _ _)] =>
        is_evar V; unify_EBeq E E
      | [E := ?V : bool |- (@eq EZ _ _)] =>
        is_evar V; unify_EBeq (#E) E
      | _ => idtac
      end;
      (*TBD - the following multimatch does too much, in that it tries
      all permutations of instantiations instead of just all
      combinations.*)
      multimatch goal with
      | [E := ?V : EB |- _] =>
        is_evar V; inst_EB E
      | [E := ?V : bool |- _] =>
        is_evar V; inst_bool E
      end;
      boom].
