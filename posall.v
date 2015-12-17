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

Require Import utils.

Ltac has_dep_prod term :=
  lazymatch term with
  | _ -> ?R => has_dep_prod R
  | forall _, _ => idtac
  end.

Ltac has_common_evar term1 term2 :=
  match term1 with
    context[?V] => 
    is_evar V;
    match term2 with context[?V1] => constr_eq V V1 end 
  end.

Ltac poser_fail_if_trivial_tac := 
  first[assumption
       |gintuition fail
       |exact True (*solve Prop/Set/Type*)
       ].

Local Ltac poser_fail_if_trivial H :=
  let T:=type of H in
  tryif assert T by (clear H;poser_fail_if_trivial_tac) then fail else idtac.

Ltac poser_btrack_initial_arg_filler := idtac.
Ltac poser_nbtrack_arg_filler := gintuition fail.

Ltac nonrec ty :=
  let rec f :=
      lazymatch goal with 
        |- ?G => 
        tryif unify G ty 
        then fail 0 ty "is not a nonrecursive type"
        else idtac end in
  let Any:=fresh in
  let x:=constr:(ltac:(clear; 
                        intro Any;
                        gintuition (f; apply Any)):((forall T, T) -> ty))
  in idtac.

Ltac nonrec_goal_type :=
  lazymatch goal with |- ?G => nonrec G end.

Ltac poser_btrack_final_arg_filler := 
  reassumption +
  (nonrec_goal_type; econstructor; poser_btrack_final_arg_filler).

Ltac poser H nH :=
  pose proof H as nH;
  let rec f :=
      let g filt :=
          idtac;
          let H':=fresh in
          (unshelve refine (let H':=_ in _));
          [..|specialize (nH H');subst H'];[filt..|f]
      in
      lazymatch type of nH with
      | ?L -> ?R =>
        tryif has_common_evar L R
        then g poser_btrack_initial_arg_filler
        else
          tryif has_dep_prod R
          then g poser_nbtrack_arg_filler
          else idtac
      | forall _, _ =>
        g poser_btrack_initial_arg_filler
      | _ => idtac
      end
  in
  f; revgoals; [|poser_btrack_final_arg_filler..];
  poser_fail_if_trivial nH.

Ltac posall H :=
  repeat let nH:=fresh "posall0" in 
         let x:=eval cbn beta zeta in ltac:(poser H nH; exact nH) in
         pose x as nH.
