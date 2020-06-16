From Base Require Export Init Equality Monad.

Instance func_Functor : Functor (func a) :=
  { map := @compose a }.

#[refine]
Instance func_FunctorL : FunctorL (func a) := {}.

Proof.
  all: now intros.
Qed.

Definition func_pure {a b} (x : b) : func a b :=
  fun _ => x.

Definition func_apply {a b c} (f : func a (b -> c)) (x : func a b) : func a c :=
  fun y => f y (x y).

Instance func_Applicative : Applicative (func a) :=
  { pure := @func_pure a
  ; apply := @func_apply a
  }.

#[refine]
Instance func_ApplicativeL : ApplicativeL (func a) := {}.

Proof.
  all: now intros.
Qed.

Definition func_bind {a b c} (x : func a b) (f : b -> func a c) : func a c :=
  fun y => f (x y) y.

Instance func_Monad : Monad (func a) :=
  { bind := @func_bind a }.

#[refine]
Instance func_MonadL : MonadL (func a) := {}.

Proof.
  all: try now intros.
  intros b c Hc Hc' f g h equ x.
  cbn.
  apply equ.
Qed.
