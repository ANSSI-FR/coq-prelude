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

Generalizable All Variables.

From Coq.Program Require Import Equality.
From Coq Require Import Setoid.

From Prelude Require Export Control Function Equality.

#[local]
Open Scope prelude_scope.

Bind Scope monad_scope with sum.

Inductive sum_equal `{Equality l, Equality r} : l + r -> l + r -> Prop :=
| equal_left (x y : l) (equ : x == y) : sum_equal (inl x) (inl y)
| equal_right (x y : r) (equ : x == y) : sum_equal (inr x) (inr y).

#[program]
Instance sum_equal_Equivalence `{Equality l, Equality r}
  : Equivalence (sum_equal (l:=l) (r:=r)).

Next Obligation.
  intros [x|x]; constructor; reflexivity.
Defined.

Next Obligation.
  intros [x|x] y equ; inversion equ; subst; constructor; now symmetry.
Defined.

Next Obligation.
  intros x [y|y] z equ1 equ2;
    inversion equ1; subst;
      inversion equ2; subst;
        constructor;
        etransitivity; eauto.
Defined.

Instance sum_Equality `{Equality l, Equality r} : Equality (l + r) :=
  { equal := sum_equal
  }.

Definition sum_map {l a b} (f : a -> b) (x : l + a) : l + b :=
  match x with
  | inr x => inr (f x)
  | inl x => inl x
  end.

#[program]
Instance sum_Functor `{Equality l} : Functor (sum l) :=
  { map := @sum_map l
  }.

Next Obligation.
  destruct x as [x|x]; reflexivity.
Defined.

Next Obligation.
  destruct x as [x|x]; reflexivity.
Defined.

Definition sum_pure {l a} (x : a) : l + a :=
  inr x.

Definition sum_app {l a b} (f : l + (a -> b)) (x : l + a) : l + b :=
  match f, x with
  | inr f, inr x => inr (f x)
  | inl e, _ | _, inl e => inl e
  end.

#[program]
Instance sum_Applicative `{Equality l} : Applicative (sum l) :=
  { pure  := @sum_pure l
  ; apply := @sum_app l
  }.

Next Obligation.
  destruct v as [x|x]; reflexivity.
Defined.

Next Obligation.
  destruct u; destruct v; destruct w; reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  destruct u; reflexivity.
Defined.

Next Obligation.
  destruct x; reflexivity.
Defined.

Definition sum_bind {l a b} (x : l + a) (f : a -> l + b) : l + b :=
  match x with
  | inr x => f x
  | inl x => inl x
  end.

#[program]
Instance sum_Monad `{Equality l} : Monad (sum l) :=
  { bind := @sum_bind l
  }.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  destruct x; reflexivity.
Defined.

Next Obligation.
  destruct f; reflexivity.
Defined.

Next Obligation.
  destruct x.
  + reflexivity.
  + apply H1.
Defined.

Next Obligation.
  reflexivity.
Defined.

(** * Why not [EitherT]

    Because of the definition of [EitherT m] (it is basically a
    wrapper arround [m (Either)]), we cannot prove the functor laws
    (and probably the other laws too).

    In order to be able to prove these laws, we need an additionnal
    law that tells [map f] is a morphism as long as [f] is a
    morphism. This works pretty great with all monads defined in
    [FreeSpec.Control], expect... [Program] (which is
    unfortunate). The reason is the definition of the [Program]
    [Equality] instance is too strong and require the results of the
    realization of two equivalent programs to be equal, not
    equivalent.

    It is not clear how hard it would be to fix that, so for now we
    have an ad-hoc solution. See the [FreeSpec.Fail] library for more
    information about that. It basically provides the necessary tools
    to promote an Interface so that the operational Semantics may
    fail. It also provides a specific monad called [FailProgram] to
    deal with the errors in a transparent manner.
 *)
