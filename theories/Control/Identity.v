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

From Prelude Require Import Control Equality.

#[local]
Open Scope prelude_scope.

Definition identity_equal `{Equality a} (x y : id a) : Prop := x == y.

Instance id_Equality `{Equality a} : Equality (id a)|1000 :=
  { equal := identity_equal
  }.

(** * Functor

 *)

Definition identity_map {a b} (f : a -> b) (x : id a) : id b :=
  f x.

#[program, universes(polymorphic)]
Instance identity_Functor : Functor id|1000 :=
  { map := @identity_map
  }.

Next Obligation.
  reflexivity.
Qed.

Next Obligation.
  reflexivity.
Defined.

Definition identity_apply {a b} (f : id (a -> b)) (x : id a) : id b :=
  f x.

Definition identity_pure {a} (x : a) : id a := x.

#[program]
Instance identity_Applicative : Applicative id|1000 :=
  { pure  := @identity_pure
  ; apply := @identity_apply
  }.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.

Definition identity_bind {a b} (x : id a) (f : a -> id b) : id b :=
  f x.

#[program]
Instance identity_Monad : Monad id|1000 :=
  { bind := @identity_bind
  }.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  reflexivity.
Defined.
