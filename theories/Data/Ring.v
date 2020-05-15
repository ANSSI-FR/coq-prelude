From Coq Require Import ZArith.
From Base Require Export Init Equality.

Class Semiring a :=
  { zero : a
  ; one : a
  ; add : a -> a -> a
  ; mul : a -> a -> a
  }.

Notation "x + y" := (add x y) : base_scope.
Notation "x * y" := (mul x y) : base_scope.

Class Semiring' (a : Type) `{EquP' a, Semiring a} : Prop :=
  { add_identity (x : a) : x + zero === x
  ; add_sym (x y : a) : x + y === y + x
  ; add_assoc (x y z : a) : (x + y) + z === x + (y + z)
  ; mul_identity (x : a) : x * one === x
  ; mul_assoc (x y z : a) : (x * y) * z === x * (y * z)
  ; mul_annihilation (x : a) : zero * x === zero
  }.

Lemma add_identity_left `{Semiring' a} (x : a) : zero + x === x.

Proof.
  rewrite (add_sym zero x).
  apply add_identity.
Qed.

Class Ring a `{Semiring a} :=
  { sub : a -> a -> a }.

Notation "x - y" := (sub x y) : base_scope.

Instance nat_Semiring : Semiring nat :=
  { zero := O
  ; one := S O
  ; add := Nat.add
  ; mul := Nat.mul
  }.

Instance nat_Ring : Ring nat :=
  { sub := Nat.sub
  }.

Instance Z_Semiring : Semiring Z :=
  { zero := 0%Z
  ; one := 1%Z
  ; add := Z.add
  ; mul := Z.mul
  }.

Instance Z_Ring : Ring Z :=
  { sub := Z.sub
  }.
