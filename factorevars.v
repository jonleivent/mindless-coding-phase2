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
  lazymatch goal with |- ?G =>
    let X:=fresh "E0" in
    set (X:=G) in *;
    factor_value_evars X;
    unfold X in *; clear X
  end.

Ltac factor_all_evars :=
  let Hs := all_hyps in
  factor_conc_evars;
  loop factor_evars Hs.

Ltac defactor_all_evars :=
  let f H := let v:=get_value H in is_evar v in
  let s H := unfold H in *; clear H in
  filter f ltac:(loop s) all_hyps.
