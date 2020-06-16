From Base Require Export Monad.

Instance id_Functor : Functor id|1000 :=
  { map := fun _ _ f x => f x }.

#[refine]
Instance id_FunctorL : FunctorL id|1000 := {}.

Proof.
  all: now intros.
Qed.

Instance id_Applicative : Applicative id|1000 :=
  { pure := fun _ x => x
  ; apply := fun _ _ f x => f x
  }.

#[refine]
Instance id_ApplicativeL : ApplicativeL id|1000 := {}.

Proof.
  all: now intros.
Qed.

Instance id_Monad : Monad id|1000 :=
  { bind := fun _ _ x f => f x }.

#[refine]
Instance id_MonadL : MonadL id|1000 := {}.

Proof.
  all: try now intros.
  intros a b Hb Hb' x f f' equ.
  apply equ.
Qed.
