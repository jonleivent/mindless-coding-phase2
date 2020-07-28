
(*Iteration over Hypotheses *)

(*fast non-kludgy versions of iteration - using dual continuations.  The icont continuation re-intros each hyp that was reverted.  The tcont continuation calls the target tac on each hyp in the desired order.  Even though these use revert/re-intro style iteration, they are about twice as fast as the hypothesis harvesting method.  The original harvesting tactics allow for much more functionality (including filtering, conditional iteration, etc.) that should be reproducible with this dual-continuation style if needed (and nothing needs them yet):*)

Ltac allhyps_bu tac :=
  idtac; (*tac runs in bottom-up hyp order, with all hyps present*)
  let rec f icont tcont :=
      idtac;
      lazymatch goal with
      | H : _ |- _ => revert H; f ltac:(intro H; icont) ltac:(tcont; tac H)
      | _ => icont; tcont
      end
  in f ltac:(idtac) ltac:(idtac).

Ltac allhyps_td tac :=
  idtac; (*tac runs in top-down hyp order, with all hyps present*)
  let rec f icont tcont :=
      idtac;
      lazymatch goal with
      | H : _ |- _ => revert H; f ltac:(intro H; icont) ltac:(tac H; tcont)
      | _ => icont; tcont
      end
  in f ltac:(idtac) ltac:(idtac).

(*The following two forms are faster than the above two, but the tac runs in a context where it is being called with other hyps reverted - hence they will not work well when tac wishes to perform actions from its target hyp onto others (such as rewrites).*)
Ltac allhyps_reverting tac :=
  idtac; (*like allhyps_bu, but runs tac on last then reverts for next *)
  lazymatch goal with
  | H : _ |- _ => tac H; revert H; allhyps_reverting tac; intro H
  | _ => idtac
  end.

Ltac allhyps_introing tac :=
  idtac; (*like allhyps_td, but reverts all then runs tac as they are reintroed*)
  lazymatch goal with
  | H : _ |- _ => revert H; allhyps_introing tac; intro H; tac H
  | _ => idtac
  end.

Inductive Stop := CStop.

(*Like the above, but uses a dedicated Stop hyp to decide when it has reintroed back to the original conclusion *)
Ltac allhyps_reverting_stop tac :=
  generalize (CStop : Stop);
  repeat lazymatch goal with
      | H : _ |- _ => tac H; revert H
      end;
  repeat lazymatch goal with
          | |- Stop -> _ => fail
          | _ => intro
         end;
  intros _.

Ltac allhyps_introing_stop tac :=
  generalize (CStop : Stop);
  repeat lazymatch goal with
         | H : _ |- _ => revert H
         end;
  repeat lazymatch goal with
         | H : Stop |- _ => fail
         | H : _ |- _ => tac H; intro
         end;
  lazymatch goal with
  | H : Stop |- _ => clear H
  end.

     
