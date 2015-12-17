Ltac revert_all :=
  repeat lazymatch goal with H:_ |- _ => revert H end.

Ltac get_value H := eval cbv delta [H] in H.

Ltac has_value H := let X:=get_value H in idtac.

Ltac minlines := 
  idtac; (*prevent early eval*)
  let stop:=fresh "stop" in
  generalize I as stop;
  revert_all;
  let rec f :=
    try (intro;
         lazymatch goal with H:?T |- _ =>
          first[constr_eq H stop; clear stop
               |let v := get_value H in
                try match goal with H' := v : T |- _ =>
                 first[constr_eq H H'; fail 1
                      |move H before H'] end; f
               |try match goal with H':T |- _ =>
                 first[constr_eq H H'; fail 1
                      |has_value H'; fail 1
                      |move H before H'] end; f
               |f] 
          end)
  in f.

Tactic Notation "onhyp'" uconstr(T) tactic3(tac) :=
  multimatch goal with H : ?T' |- _ => unify T T'; tac H end.

Tactic Notation "onhyp" open_constr(T) tactic3(tac) := onhyp' T tac.

Ltac is_head_of head type :=
  lazymatch type with
  | head => idtac
  | ?H ?T => is_head_of head H
  end.

Tactic Notation "onhead" constr(head) tactic3(tac) :=
  multimatch goal with H : ?T |- _ => is_head_of head T; tac H end.

Ltac destr H := destruct H.
Ltac induct H := induction H.
Ltac invert H := inversion H.

Ltac cleanup_tac := 
  tauto||congruence||(constructor;cleanup_tac).

Tactic Notation "clean" "using" tactic(tac) :=
  repeat match goal with 
           H : ?T |- _ => clear H; assert T as _ by tac end.

Ltac clean := clean using cleanup_tac.

Ltac destruct_goal_bool :=
  match goal with
  | B : bool |- context[?G] => constr_eq B G; destruct B
  end.

Ltac destruct_useful_bool :=
  onhead bool (fun B =>
                 lazymatch goal with
                   _ : context [B] |- _ =>
                   destruct B
                 end).

Ltac deconj := repeat apply conj.

Ltac unsetall :=
  repeat lazymatch goal with H := _ |- _ => unfold H in *; clearbody H end.

Ltac simple_reflex :=
  lazymatch goal with
  | |- ?X = ?X => reflexivity
  | |- ?L = ?R =>
    first[is_evar L|is_evar R]; unify L R; reflexivity
  end.

Local Lemma feq : forall {A B} (f g : A -> B) (x y : A), f=g -> x=y -> f x = g y.
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Local Lemma depfeq : forall {A B}(f g : forall x:A, B x), f=g -> forall x, f x = g x.
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Ltac my_f_equal :=
  try simple_reflex;
  lazymatch goal with
  | |- ?f ?x = ?g ?x => apply (depfeq f g); my_f_equal
  | _ => try (apply feq; [my_f_equal|try simple_reflex])
  end.

Tactic Notation "force" "exact" constr(H) :=
  let tH:=type of H in
  lazymatch goal with
    |- ?G => replace G with tH; [exact H|my_f_equal]
  end.

Tactic Notation "force" "refine" uconstr(X) "by" tactic1(tac) :=
  let H:=fresh in
  lazymatch goal with
    |- ?G =>
    refine (let H:=X in _);
    cycle -1;
    [let tH:=type of H in
     replace G with tH;
     [exact H|clear H;my_f_equal;[tac..]]|..]
  end.

Ltac reassumption :=
  multimatch goal with H:_ |- _ => exact H end.

Ltac vgoal := 
  idtac; (*prevents early eval*)
  match reverse goal with
    | H : ?T |- _ => 
      first[let v := get_value H in 
            idtac H ":=" v ":" T
           |idtac H ":" T];
      fail
    | |- ?G => 
      idtac "======"; idtac G; idtac ""
  end.

Ltac dintros :=
  intros;
  repeat (match goal with
           | H : _ /\ _ |- _ => destruct H as (? & ?)
           end);
  subst.
