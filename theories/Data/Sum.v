From Base Require Import Monad.

Definition sum_map {a b c} (f : b -> c) (x : a + b) : a + c :=
  match x with
  | inr x => inr (f x)
  | inl x => inl x
  end.

Instance sum_Functor : Functor (sum a) :=
  { map := @sum_map a }.

#[refine]
Instance sum_FunctorL : FunctorL (sum a) := {}.

Proof.
  + now intros b Hb Hb' [ x | x ].
  + now intros b c d Hd Hd' u v [ x | x ].
Qed.

Definition sum_pure {a b} (x : b) : a + b :=
  inr x.

Definition sum_apply {a b c} (f : a + (b -> c)) (x : a + b) : a + c :=
  match f, x with
  | inr f, inr x => inr (f x)
  | inl x, _ => inl x
  | _, inl x => inl x
  end.

Instance sum_Applicative : Applicative (sum a) :=
  { pure := @sum_pure a
  ; apply := @sum_apply a
  }.

#[refine]
Instance sum_ApplicativeL : ApplicativeL (sum a) := {}.

Proof.
  + now intros b Hb Hb' [ v | v ].
  + now intros b c d Hd Hd' [ u | u ] [ v | v] [ w | w ].
  + now intros b c Hc Hc' v x.
  + now intros b c Hb Hb' [ u | u ] y.
  + now intros b c Hc Hc' g [ x | x].
Qed.

Definition sum_bind {a b c} (x : a + b) (f : b -> a + c) : a + c :=
  match x with
  | inr x => f x
  | inl x => inl x
  end.

Instance sum_Monad : Monad (sum a) :=
  { bind := @sum_bind a }.

#[refine]
Instance sum_MonadL : MonadL (sum a) := {}.

Proof.
  + now intros b c Hc Hc' x f.
  + now intros b Hb Hb' [ x | x ].
  + now intros b c d Hd Hd' [ f | f ] g h.
  + intros b c Hc Hc' [ x | x ] f f' equ; [ reflexivity |].
    apply equ.
  + now intros b c Hc Hc' [ x | x ] f.
Qed.

Module SumExtraction.
  Extract Inductive sum => "Coqbase.Sum.t" ["Coqbase.Sum.Inl" "Coqbase.Sum.Inr"].
  Extraction Inline sum_Applicative.
End SumExtraction.
