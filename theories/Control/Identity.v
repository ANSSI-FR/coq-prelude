(* coq-prelude
 * Copyright (C) 2018 ANSSI
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

Require Import Prelude.Control.
Require Import Prelude.Equality.

Local Open Scope prelude_scope.

Record Identity
       (a:  Type)
  := identity { runIdentity: a
              }.

Arguments runIdentity [a] (_).
Arguments identity [a] (_).

Notation "! a" :=
  (runIdentity a)
    (at level 41, right associativity)
  : prelude_scope.


Definition identity_equal
           {a:    Type} `{Equality a}
           (x y:  Identity a)
  : Prop :=
  !x == !y.

Lemma identity_equal_refl
      {a:  Type} `{Equality a}
      (x:  Identity a)
  : identity_equal x x.
Proof.
  unfold identity_equal.
  reflexivity.
Qed.

Lemma identity_equal_sym
      {a:    Type} `{Equality a}
      (x y:  Identity a)
  : identity_equal x y
    -> identity_equal y x.
Proof.
  unfold identity_equal.
  intro H'.
  symmetry.
  exact H'.
Qed.

Lemma identity_equal_trans
      {a:      Type} `{Equality a}
      (x y z:  Identity a)
  : identity_equal x y
    -> identity_equal y z
    -> identity_equal x z.
Proof.
  unfold identity_equal.
  intros X Y.
  rewrite X.
  exact Y.
Qed.

Add Parametric Relation
    (a:  Type) `{Equality a}
  : (Identity a) (identity_equal)
    reflexivity  proved by identity_equal_refl
    symmetry     proved by identity_equal_sym
    transitivity proved by identity_equal_trans
      as identity_equal_equiv.

Instance identity_Equal
         (a:  Type) `{Equality a}
  : Equality (Identity a) :=
  { equal := identity_equal
  }.

Lemma wrap_unwrap_identity
      {a:  Type} `{Equality a}
      (x:  Identity a)
  : identity (! x) == x.
Proof.
  destruct x.
  reflexivity.
Qed.

Lemma wrap_identity_equal
      {a:    Type} `{Equality a}
      (x y:  a)
  : x == y <-> identity x == identity y.
Proof.
  split.
  + intro Heq.
    cbn; unfold identity_equal.
    exact Heq.
  + intro Heq.
    cbn in *.
    unfold identity_equal in Heq.
    exact Heq.
Qed.

Lemma unwrap_identity_equal
      {a:    Type} `{Equality a}
      (x y:  Identity a)
  : !x == !y <-> x == y.
Proof.
  destruct x as [x]; destruct y as [y].
  cbn.
  exact (wrap_identity_equal x y).
Qed.

(** * Functor

 *)

Definition identity_map
           (a b:  Type)
           (f:    a -> b)
           (x:    Identity a)
  : Identity b :=
  identity (f (!x)).

Instance identity_Functor
  : Functor Identity :=
  { map := identity_map
  }.
Proof.
  + intros a H x.
    unfold identity_map; unfold id.
    apply wrap_unwrap_identity.
  + intros a b c H u v x.
    apply wrap_identity_equal.
    reflexivity.
Defined.

Definition identity_apply
           (a b:  Type)
           (f:    Identity (a -> b))
           (x:    Identity a)
  : Identity b :=
  identity ((!f) (!x)).

Definition identity_pure
           (a:  Type)
           (x:  a)
  : Identity a :=
  identity x.

Instance identity_Applicative
  : Applicative Identity :=
  { pure  := identity_pure
  ; apply := identity_apply
  }.
Proof.
  + intros; apply <- wrap_identity_equal; reflexivity.
  + intros; apply <- wrap_identity_equal; reflexivity.
  + intros; apply <- wrap_identity_equal; reflexivity.
  + intros; apply <- wrap_identity_equal; reflexivity.
  + intros; apply <- wrap_identity_equal; reflexivity.
Defined.

Definition identity_bind
           (a b:  Type)
           (x:    Identity a)
           (f:    a -> Identity b)
  : Identity b :=
  f (!x).

Instance identity_Monad
  : Monad Identity :=
  { bind := identity_bind
  }.
Proof.
  + intros; apply wrap_identity_equal; reflexivity.
  + intros; apply <- wrap_identity_equal; reflexivity.
  + intros a b c C f g h.
    unfold identity_bind.
    reflexivity.
  + intros a b H x f f' Heq.
    cbn.
    unfold identity_equal, identity_bind.
    destruct x.
    cbn in *.
    unfold function_equal in Heq.
    apply unwrap_identity_equal.
    apply Heq.
  + intros; apply <- wrap_identity_equal; reflexivity.
Defined.