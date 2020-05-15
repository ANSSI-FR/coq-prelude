From Coq Require Export List Extraction Eqdep.
Export ListNotations.

#[global]
Generalizable All Variables.

(* This scope is used for typeclass-based notations. *)
Declare Scope base_scope.
Delimit Scope base_scope with base.
#[global] Open Scope base_scope.
#[global] Close Scope nat_scope.
#[global] Open Scope bool_scope.

#[local] Set Universe Polymorphism.

Definition id {a : Type} (x : a) : a := x.

Definition compose {a b c} (g : b -> c) (f : a -> b) : a -> c :=
  fun (x: a) => g (f x).

Notation "f <<< g" := (compose f g) (at level 50) : function_scope.
Notation "f >>> g" := (compose g f) (at level 50) : function_scope.

Definition func (a b : Type) := a -> b.

Bind Scope function_scope with func.

(** [ssubst] will deal with hypotheses of the form [existT _ _ x =
    existT _ _ y] *)

Ltac ssubst :=
  lazymatch goal with
| [ H : existT _ _ _ = existT _ _ _ |- _ ]
  => apply Eqdep.EqdepTheory.inj_pair2 in H; ssubst
| [ |- _] => subst
end.
