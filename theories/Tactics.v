Require Import Coq.Logic.Eqdep.

(** [dup H H'] will duplicate the hypothesis [H], under the name [H'].
    *)
Ltac dup H H' :=
  pose proof H as H'.

(** [ssubst] will deal with hypotheses of the form [existT _ _ x =
    existT _ _ y] *)
Ltac ssubst :=
  lazymatch goal with
| [ H : existT _ _ _ = existT _ _ _ |- _ ]
  => apply Eqdep.EqdepTheory.inj_pair2 in H;
     ssubst
| [ |- _]
  => subst
end.
