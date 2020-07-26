
(* Find all evars in a goal, and migrate them into standalone bodies
of local defs - so that every evar in the goal exists only as such a
standalone body.

This currently only works for evars that are not under binders.
*)

Require Import hypiter.

Ltac get_value H := eval cbv delta [H] in H.

Ltac has_value H := let x:=get_value H in idtac.

Ltac factor_value_evars H :=
  repeat 
    let vH:=get_value H in
    has_evar vH;
    match vH with
      context[?E] =>
      is_evar E;
        let nE:=fresh "E0" in
        set (nE:=E) in *
    end.

Ltac factor_type_evars H :=
  repeat
    let tH:=type of H in
    has_evar tH;
    match tH with
      context[?E] =>
      is_evar E;
        let nE:=fresh "E0" in
        set (nE:=E) in *
    end.

Ltac factor_evars H :=
  factor_value_evars H;
  factor_type_evars H.

Ltac factor_conc_evars :=
  repeat
    match goal with
      |- context[?E] =>
      is_evar E;
      let nE := fresh "E0" in
      set (nE := E) in *
    end.

Ltac factor_hyp_evars :=
  allhyps_td factor_evars.

Ltac factor_all_evars :=
  factor_hyp_evars;
  factor_conc_evars.

Ltac defactor_all_evars :=
  let f H := try (let v:=get_value H in
                  is_evar v; unfold H in *; clear H)
  in
  allhyps_td f.

Ltac clearbody_evars :=
  let f H := try (let v:=get_value H in
                 is_evar v; clearbody H)
  in
  allhyps_td f.
