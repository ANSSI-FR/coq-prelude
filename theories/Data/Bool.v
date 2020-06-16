From Base Require Import Equality.

Instance bool_Equ : Equ bool :=
  { equalb := Bool.eqb }.

#[program]
Instance bool_EquL : EquL bool.

Next Obligation.
  now rewrite Bool.eqb_true_iff.
Qed.

Module BoolExtraction.
  Extract Inductive bool => bool ["true" "false"].
  Extract Inlined Constant andb => "(&&)".
  Extract Inlined Constant orb => "(||)".
  Extract Constant negb => "Bool.not".
End BoolExtraction.
