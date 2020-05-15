From Base Require Import Init.
From Coq Require Export Equivalence Setoid Morphisms.

Class EquP (a : Type) : Type := { equal : a -> a -> Prop }.

Instance default_EquP : EquP a|10000 := { equal := eq }.

Class Equ (a : Type) : Type := { equalb : a -> a -> bool }.

Infix "===" := equal (at level 70, no associativity) : base_scope.
Notation "x '!==' y" := (~ equal x y) (at level 70, no associativity)
  : base_scope.

Infix "==" := equalb (at level 70, no associativity) : base_scope.
Notation "x != y" := (negb (equalb x y)) (at level 70, no associativity)
  : base_scope.

Class EquP' (a : Type) `{H : EquP a} : Type :=
  { equp_is_equivalence :> Equivalence (@equal a H) }.

Instance default_EquP' : EquP' a|10000 := {}.

Class Equ' (a : Type) `{EquP' a, Equ a} : Type :=
  { equal_equalb_equiv : forall (x y : a), x === y <-> x == y = true }.

Arguments equal_equalb_equiv [a _ _ _ _] (x y).

Instance func_EquP `(EquP b) : EquP (func a b) :=
  { equal := fun f g => forall x, f x === g x }.

#[refine]
Instance func_EquP' `(EquP' b) : EquP' (func a b) := {}.

Proof.
  constructor.
  + unfold Reflexive.
    now intros.
  + unfold Symmetric.
    intros f g equ x.
    now symmetry.
  + unfold Transitive.
    intros f g h equ1 equ2 x.
    transitivity (g x); [ apply equ1 | apply equ2 ].
Qed.

Ltac morphism_signature a :=
  match a with
  | ?a -> ?b => exact ((@equal a _) ==> ltac:(morphism_signature b))%signature
  | ?b => exact (@equal b _)
  end.

Ltac equ_morphism a :=
  match type of a with
  | ?t => exact (Proper ltac:(morphism_signature t) a)
  end.

Notation "'EquMorphism' x" :=
  ltac:(equ_morphism x) (at level 200, only parsing) : base_scope.
