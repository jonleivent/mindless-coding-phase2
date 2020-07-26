
(*Iteration over Hypotheses *)

(*fast non-kludgy versions of iteration - using dual continuations.  The icont continuation re-intros each hyp that was reverted.  The tcont continuation calls the target tac on each hyp in the desired order.  Even though these use revert/re-intro style iteration, they are about twice as fast as the hypothesis harvesting method.  The original harvesting tactics allow for much more functionality (including filtering, conditional iteration, etc.) that should be reproducible with this dual-continuation style if needed (and nothing needs them yet):*)

Ltac allhyps_bu tac := (*tac runs in bottom-up hyp order*)
  let rec f icont tcont :=
      idtac;
      lazymatch goal with
      | H : _ |- _ => revert H; f ltac:(intro H; icont) ltac:(tcont; tac H)
      | _ => icont; tcont
      end
  in f ltac:(idtac) ltac:(idtac).

Ltac allhyps_td tac := (*tac runs in top-down hyp order*)
  let rec f icont tcont :=
      idtac;
      lazymatch goal with
      | H : _ |- _ => revert H; f ltac:(intro H; icont) ltac:(tac H; tcont)
      | _ => icont; tcont
      end
  in f ltac:(idtac) ltac:(idtac).
