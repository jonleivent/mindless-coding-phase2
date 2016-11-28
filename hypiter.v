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

(*Iteration over Hypotheses

In order to simplify iteration over hypotheses in a goal, we first "harvest"
together the hyps into a single term that can be easily pulled apart one hyp
at a time.  There is a very simple way to do this using the fact that the
constructor tactic can can construct a function of any number of arguments of
any type that returns some easily constructed type, such as True.  We then use
the tactic-in-term construct ltac:(...) to create the desired goal type by
reverting or generalizing the hyptheses we want to be part of it.  The
resulting constr will be a function application, where the hyps are the args -
and so can be popped off at the right.  *)

Ltac harvest_hyps harvester :=
  constr:(ltac:(harvester; constructor) : True).

Tactic Notation "harvest" tactic3(harvester) "=>" tactic3(tac) :=
  (* Typical harvesters are "generalize hs" and "revert_clearbody_all" *)
  let hs := harvest_hyps harvester in
  tac hs.

Ltac last_hyp :=
  lazymatch goal with H : _ |- _ => H end.

Ltac revert_clearbody H := try clearbody H; revert H.

Ltac revert_clearbody_all :=
  repeat revert_clearbody last_hyp.

Ltac all_hyps := harvest_hyps revert_clearbody_all.

(*All hyps in the usual bottom-up order:*)
Tactic Notation "hyps" "=>" tactic3(tac) :=
  harvest revert_clearbody_all => tac.

(*Just the specified hyps*)
Tactic Notation "hyps" ne_hyp_list(hs) "=>" tactic3(tac) :=
  harvest generalize hs => tac.

(*next_hyp is the basic iteration-building component for iterating
over hypotheses*)
Ltac next_hyp hs step last := 
  lazymatch hs with 
  | (?hs' ?H) => step H hs'
  | _ => last
  end.

(*Normal forward loop (bottom-up hypotheses)
For example, to loop over all hyps:
  hyps => loop tac.
where tac is a function of a single hyp.
*)
Ltac loop tac hs :=
  idtac;
  let rec step H hs := tac H; next_hyp hs step idtac in
  next_hyp hs step idtac.

Ltac next_hyp2 hs step acc :=
  lazymatch hs with
  | (?hs' ?H) => step H acc hs'
  | _ => acc
  end.

Ltac ufold tac acc hs :=
  let rec step H a hs := let b:=tac H a in next_hyp2 hs step b in
  next_hyp2 hs step acc.

Ltac dfold tac acc hs :=
  let rec step H a hs := let b:=next_hyp2 hs step a in tac H b in
  next_hyp2 hs step acc.

(*Forward iteration that stops instead of failing when tac fails at
level 0 (fail higher to undo the iteration) *)
Ltac tryloop tac hs :=
  idtac;
  let rec step H hs := 
      tryif tac H then next_hyp hs step idtac else idtac in
  next_hyp hs step idtac.

(*Forward iteration with a separate cond test - iteration of tac
continues while cond is true. *)
Ltac while cond tac hs :=
  idtac;
  let rec step H hs := 
      tryif cond H then tac H; next_hyp hs step idtac else idtac in
  next_hyp hs step idtac.

(*Similar iterator variants (try, while) are possible with the
following as well:*)

(*Normal reverse loop (top-down hypotheses) *)
Ltac rloop tac hs :=
  idtac;
  let rec step H hs := next_hyp hs step idtac; tac H in
  next_hyp hs step idtac.

(*Backtrack-capable choice*)
Ltac plusses tac hs :=
  idtac;
  let rec step H hs := tac H + next_hyp hs step fail in
  next_hyp hs step fail.

(*Non-backtrack-cabable choice via first*)
Ltac firsts tac hs :=
  idtac;
  let rec step H hs := first[tac H | next_hyp hs step fail] in
  next_hyp hs step fail.

(*Non-backtrack-capable choice via ||*)
Ltac bars tac hs :=
  idtac;
  let rec step H hs := tac H || next_hyp hs step fail in
  next_hyp hs step fail.

(*Other interesting hyp harvester functions:*)

Ltac clear_through H :=
  let H':= last_hyp in
  clear H';
   first[ constr_eq H' H 
        | clear_through H].

Ltac revert_clearbody_below H :=
  let H':=last_hyp in
  first [ constr_eq H' H
        | try clearbody H';
          revert H'; 
          revert_clearbody_below H].

(*Modifiers of harvested hypotheses:*)

(*negation*)
Ltac neg tac hs :=
  idtac;
  let gen_if_absent H := 
      match hs with context[H] => idtac | _ => generalize H end in
  harvest (hyps => loop gen_if_absent) => tac.

(*With negation, we can do hyps -, which excludes specific hyps:*)
Tactic Notation "hyps" "-" hyp_list(hs) "=>" tactic3(tac) :=
  harvest generalize hs => neg tac.

(*inclusion based on predicate (filt)*)
Ltac filter filt tac hs :=
  let g H := idtac;tryif filt H then generalize H else idtac in
  harvest loop g hs => tac.

(*inclusion based on type*)
Ltac filter_type type :=
  let filt H := let tH:=type of H in constr_eq tH type in
  filter filt.

Ltac gen H := generalize H.

(*inclusion based on position above hyp H*)
Ltac above H tac hs :=
  idtac;
  let gen := clear_through H; loop gen hs in
  harvest gen => tac.

(*inclusion based on position below hyp H*)
Ltac below H tac hs :=
  harvest revert_clearbody_below H => tac.

(*adding H to front of iteration*)
Ltac firstly H tac hs :=
  idtac;
  let gen := generalize H; loop gen hs in
  harvest gen => tac.

(*adding H to back of iteration*)
Ltac lastly H tac hs :=
  idtac;
  let g := loop gen hs; generalize H in
  harvest g => tac.

(*reversing the order*)
Ltac reverse tac hs :=
  harvest rloop gen hs => tac.
