
Require Export mindless.erasable.
Import ErasableNotation.
Require Export Coq.ZArith.ZArith.
Require Import mindless.utils.
Require Import mindless.factorevars.
Require Import mindless.hypiter.
Require Import Coq.micromega.Lia.

Notation EZ := ##Z (only parsing).

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

Declare Scope E_scope.
Notation "x + y" := (ezadd x y) : E_scope.
Notation "x - y" := (ezsub x y) : E_scope.
Notation "- x" := (ezopp x) : E_scope.
Notation "x * y" := (ezmul x y) : E_scope.

Notation "x < y" := ((liftP2 Z.lt) x y) : E_scope.
Notation "x > y" := ((liftP2 Z.gt) x y) : E_scope.
Notation "x <= y" := ((liftP2 Z.le) x y) : E_scope.
Notation "x >= y" := ((liftP2 Z.ge) x y) : E_scope.

Opaque Z.mul.

Notation EB := ##bool (only parsing).

Definition Enegb := lift1 negb.

Definition b2Z(b : bool) : Z := if b then 1 else 0.
Definition Eb2Z := lift1 b2Z.

Notation "^ b" := (b2Z b) (at level 30, format "^ b") : Z_scope.
Notation "^ b" := (Eb2Z b) (at level 30, format "^ b") : E_scope.

Lemma b2Zbounds : forall b, ^b >= 0 /\ ^b <= 1.
Proof.
  dintros.
  destruct b; cbn; lia.
Qed.

(* How should we classify rewrite rules?  By their applicability -
meaning by the type of formula in which they would have a chance of
rewriting something. *)

(*Set Default Proof Using "Type".
Set Proof Using Clear Unused.*)

Set Default Proof Using "Type".
Set Suggest Proof Using.

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
    clear; unerase; cbn; autorewrite with bool_term_rws bool_eq_rws unerase_rws; tauto.

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
     Enegbf_rw Enegbt_rw Edubnegb_rw
  : EB_term_rws simp_rws term_rws.

Hint Rewrite
     Eteqt_rw Efeqf_rw Eteqf_rw Efeqt_rw Ebneq_rw Enegbfl_rw Enegbfr_rw
     Enegbtl_rw Enegbtr_rw Enegb_inj_rw
  : EB_eq_rws eq_rws.

Section EZ_Desharping_Rewrites.
  Variables m n : Z.
  Variable b : bool.

  Tactic Notation "!!" := clear; cbn; reflexivity.
  Open Scope E_scope.
  Lemma eadd_desharp_rw : (#n + #m) = #(n + m)%Z. Proof. !!. Qed.
  Lemma esub_desharp_rw : (#n - #m) = #(n - m)%Z. Proof. !!. Qed.
  Lemma emul_desharp_rw : (#n * #m) = #(n * m)%Z. Proof. !!. Qed.
  Lemma eopp_desharp_rw : - #n = #(- n)%Z. Proof. !!. Qed.
  Lemma Enegb_desharp_rw : Enegb #b = #(negb b). Proof. !!. Qed.
  Lemma Eb2Z_desharp_rw : ^#b = #(^b)%Z. Proof. !!. Qed.

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
  Lemma b2Zt_rw : ^true = 1. Proof. !!. Qed.
  Lemma b2Zf_rw : ^false = 0. Proof. !!. Qed.
  Lemma b2Z_negb_rw : ^(negb b) = 1 - ^b. Proof. !!. Qed.

  (*b2Z equality rewrites*)
  Lemma b2Z_inj_rw : ^b1 = ^b2 <-> b1 = b2. Proof. !!. Qed.
  Lemma b2Zeq1l_rw : ^b = 1 <-> b = true. Proof. !!. Qed.
  Lemma b2Zeq1r_rw : 1 = ^b <-> b = true. Proof. !!. Qed.
  Lemma b2Zeq0l_rw : ^b = 0 <-> b = false. Proof. !!. Qed.
  Lemma b2Zeq0r_rw : 0 = ^b <-> b = false. Proof. !!. Qed.
  Lemma b2Zeq1mb2Z_rw : ^b1 = 1 - ^b2 <-> b1 = negb b2. Proof. !!. Qed.
  Lemma b2Zeq1mb2Zs_rw : 1 - ^b2 = ^b1 <-> b1 = negb b2. Proof. !!. Qed.
  Lemma b2Zeqnb2Zp1_rw : ^b1 = - ^b2 + 1 <-> b1 = negb b2. Proof. !!. Qed.
  Lemma b2Zeqnb2Zp1s_rw : - ^b2 + 1 = ^b1 <-> b1 = negb b2. Proof. !!. Qed.

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
    clear; unerase; autorewrite with b2Z_term_rws b2Z_eq_rws; tauto.
  Open Scope E_scope.
  (*Eb2Z term rewrites*)
  Lemma Eb2Zt_rw : ^#true = #1. Proof. !!. Qed.
  Lemma Eb2Zf_rw : ^#false = #0. Proof. !!. Qed.
  Lemma Eb2Z_negb_rw : ^(Enegb b) = #1 - ^b. Proof. !!. Qed.

  (*Eb2Z equality rewrites*)
  Lemma Eb2Z_inj_rw : ^b1 = ^b2 <-> b1 = b2. Proof. !!. Qed.
  Lemma Eb2Zeq1l_rw : ^b = #1 <-> b = #true. Proof. !!. Qed.
  Lemma Eb2Zeq1r_rw : #1 = ^b <-> b = #true. Proof. !!. Qed.
  Lemma Eb2Zeq0l_rw : ^b = #0 <-> b = #false. Proof. !!. Qed.
  Lemma Eb2Zeq0r_rw : #0 = ^b <-> b = #false. Proof. !!. Qed.
  Lemma Eb2Zeq1mb2Z_rw : ^b1 = #1 - ^b2 <-> b1 = Enegb b2. Proof. !!. Qed.
  Lemma Eb2Zeq1mb2Zs_rw : #1 - ^b2 = ^b1 <-> b1 = Enegb b2. Proof. !!. Qed.
  Lemma Eb2Zeqnb2Zp1_rw :
    ^b1 = - ^b2 + #1 <-> b1 = Enegb b2. Proof. !!. Qed.
  Lemma Eb2Zeqnb2Zp1s_rw :
    - ^b2 + #1 = ^b1 <-> b1 = Enegb b2. Proof. !!. Qed.

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

  Tactic Notation "!!" := lia.

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

  Tactic Notation "!!" := clear; unerase; lia.
  Open Scope E_scope.
  Lemma Ezlhs_rw : x = y <-> x - y = #0. Proof. !!. Qed.
  Lemma Ezadd1_lhs_rw : x + y = z <-> x = z - y. Proof. !!. Qed.
  Lemma Ezadd2_lhs_rw : x + y = z <-> y = z - x. Proof. !!. Qed.
  Lemma Ezsub1_lhs_rw : x - y = z <-> x = z + y. Proof. !!. Qed.
  Lemma Ezsub2_lhs_rw : x - y = z <-> y = x - z. Proof. !!. Qed.
  Lemma Ezopp_lhs_rw : - x = y <-> x = - y. Proof. !!. Qed.

  Lemma Eziso1_rw : y = #0 <-> x = x + y. Proof. !!. Qed.
  Lemma Eziso2_rw : y = #0 <-> x = x - y. Proof. !!. Qed.

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
                 (*cannot be decidable, because no equality function is: EZ -> EZ -> bool*)
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
  tryif first [constr_eq tT Z|constr_eq tT (##Z)]
  then let e:=fresh in
       let ee:=fresh in
       remember T as e eqn:ee in *;
       (*safe_ring_simplify_in ee;*) try ring_simplify in ee;
       (*do not use subst e - it causes problems*)
       rewrite ?ee in *; clear e ee
  else (rsimp_term F; rsimp_term A).

Ltac rsimp_in H :=
  try rewrite Ezlhs_rw in H;
  try rewrite zlhs_rw in H;
  autorewrite with ensharping_rws in H;
  autorewrite with term_rws in H;
  let T:=type of H in rsimp_term T.

Ltac rsimp_conc :=
  try rewrite Ezlhs_rw;
  try rewrite zlhs_rw;
  autorewrite with ensharping_rws;
  autorewrite with term_rws;
  lazymatch goal with
  | |- ?G => rsimp_term G
  end.

Ltac try_rsimp_in H := try rsimp_in H.

Ltac rsimp :=
  rsimp_conc;
  allhyps_td try_rsimp_in.

(************************************************************************)

Hint Rewrite <- b2Z_inj_rw : bang_rws.

Ltac bang_setup_tactic := idtac. (*to be redefined*)

Ltac pose_b2Zbounds :=
  let f H := try pose proof (b2Zbounds H) in
  allhyps_bu f;
  pose proof (b2Zbounds true);
  pose proof (b2Zbounds false).
    
Ltac bang_internal setup :=
  dintros;
  unsetall;
  try tauto;
  first[check_in_prop|exfalso];
  setup;
  unerase;
  autorewrite with bang_rws in *;
  pose_b2Zbounds;
  (lia ||
   lazymatch goal with
   | |- _ /\ _ => deconj; first[congruence|lia]
   | _ => congruence
   end).

Ltac bang := bang_internal bang_setup_tactic.
Ltac bang0 := bang_internal idtac.

Ltac clear_evars :=
  (*assumes all evars are factored*)
  repeat match goal with
         | H := ?V |- _ => is_evar V; clearbody H
         end.

Ltac hyps_have_evars :=
  (*assumes all evars are factored*)
  match goal with
    H := ?V |- _ =>
    is_evar V;
    lazymatch goal with
    | _ : context[H] |- _ => idtac
    | _ := context[H] |- _ => idtac
    end
  end.

Ltac nbang :=
  (*assumes all evars are factored*)
  intros;
  tryif hyps_have_evars then idtac
  else
  lazymatch goal with
    |- ?G =>
    tryif (let x := constr:((ltac:(intros; clear_evars; bang)):(G -> False)) in idtac)
    then fail
    else idtac
  end.

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

Ltac unify_evar E V :=
  (*instantiate (1:=V) in (Value of E).*)
  let Ee := get_value E in
  is_evar Ee;
  tryif constr_eq Ee V
  then fail
  else unify Ee V.

Ltac inst_bool E :=
  ((multimatch goal with
     | b := ?V : bool |- _ =>
       is_evar V;
       (unify_evar E (V) +
        unify_evar E (negb V))
     end) +
   (unify_evar E (true)) +
   (unify_evar E (false)) +
   (multimatch goal with
     | b : bool |- _ =>
       tryif has_value b
       then fail
       else (unify_evar E (b) +
             unify_evar E (negb b))
     end));
  unfold E in *; clear E.

Ltac inst_EB E :=
  ((multimatch goal with
     | b := ?V : EB |- _ =>
       is_evar V;
       (unify_evar E (V) +
        unify_evar E (Enegb V))
     | b := ?V : bool |- _ =>
       is_evar V;
       (unify_evar E (#V) +
        unify_evar E (Enegb #V))
     end) +
   (unify_evar E (#true)) +
   (unify_evar E (#false)) +
   (multimatch goal with
     | b : EB |- _ =>
       tryif has_value b
       then fail
       else (unify_evar E (b) +
             unify_evar E (Enegb b))
     | b : bool |- _ =>
       tryif has_value b
       then fail
       else (unify_evar E (#b) +
             unify_evar E (Enegb #b))
     end));
  unfold E in *; clear E.

Ltac unify_booleq E :=
  first [rewrite (Eziso1_rw (Eb2Z #E));
          ring_simplify; notin_conc_rhs E
        |rewrite (Eziso2_rw (Eb2Z #E));
          ring_simplify; notin_conc_rhs E];
  autorewrite with Eb2Z_eq_rws;
  autorewrite with desharping_rws;
  defactor_all_evars;
  reflexivity.

Ltac unify_EBeq E :=
  first [rewrite (Eziso1_rw (Eb2Z E));
          ring_simplify; notin_conc_rhs E
        |rewrite (Eziso2_rw (Eb2Z E));
          ring_simplify; notin_conc_rhs E];
  autorewrite with Eb2Z_eq_rws;
  defactor_all_evars;
  reflexivity.

Ltac unify_Zeq E :=
  first[rewrite (Eziso1_rw #E);
         ring_simplify; notin_conc_rhs E
       |rewrite (Eziso2_rw #E);
        ring_simplify; notin_conc_rhs E];
  autorewrite with desharping_rws;
  defactor_all_evars;
  reflexivity.

Ltac unify_EZeq E :=
  first[rewrite (Eziso1_rw E);
         ring_simplify; notin_conc_rhs E
       |rewrite (Eziso2_rw E);
         ring_simplify; notin_conc_rhs E];
  defactor_all_evars;
  reflexivity.

Ltac boom_internal doinsts :=
  dintros;
  defactor_all_evars;
  lazymatch goal with
  | |- (@eq EB _ _) => try reflexivity; rewrite <-Eb2Z_inj_rw
  | _ => idtac
  end;
  rsimp_conc;
  try simple_reflex;
  factor_all_evars;
  match goal with
  | [E := ?V : Z |- (@eq EZ _ _)] => is_evar V; unify_Zeq E
  | [E := ?V : EZ |- (@eq EZ _ _)] => is_evar V; unify_EZeq E
  | [E := ?V : EB |- (@eq EZ _ _)] => is_evar V; unify_EBeq E
  | [E := ?V : bool |- (@eq EZ _ _)] => is_evar V; unify_booleq E
  | _ =>  try bang
  end;
  match goal with
  | [E := ?V : EB |- _] => is_evar V
  | [E := ?V : bool |- _] => is_evar V
  end;
  check_in_prop;
  lazymatch doinsts with
  | 0 => idtac
  | false => fail "boom prevented from trying bool/EB instantiations"
  | true => nbang
  | I => shelve
  end;
  (*TBD - the following multimatch does too much, in that it tries all
    permutations of instantiations instead of just all combinations.*)
  multimatch goal with
  | [E := ?V : EB |- _] => is_evar V; inst_EB E; boom_internal 0
  | [E := ?V : bool |- _] => is_evar V; inst_bool E; boom_internal 0
  end.

Ltac boom := boom_internal 0.
