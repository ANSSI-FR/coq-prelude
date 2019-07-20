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

From Coq Require Import Basics FunctionalExtensionality.
From Prelude Require Import Control Equality.

#[local]
Open Scope prelude_scope.

Definition func (a b : Type) := a -> b.

Bind Scope monad_scope with func.
Bind Scope function_scope with func.

Definition map_func {a b c} (f : b -> c) (g : func a b) : func a c :=
  fun (x : a) => f (g x).

#[program]
Instance func_Functor (a : Type) : Functor (func a) :=
  { map := @map_func a
  }.

Next Obligation.
  (* functor identity *)
  reflexivity.
Defined.

Next Obligation.
  (* functor composition *)
  reflexivity.
Defined.

Definition func_apply {a b c} (f : func a (b -> c)) (g : func a b) : func a c :=
  fun (x : a) => f x (g x).

Definition func_pure {a b} (x : b) : func a b :=
  fun (_ : a) => x.

#[program]
Instance func_Applicative (a:  Type) : Applicative (func a) :=
  { pure  := @func_pure a
  ; apply := @func_apply a
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

Definition func_bind {a b c} (f : func a b) (g : b -> func a c) : func a c :=
  fun (x : a) => g (f x) x.

#[program]
Instance func_Monad (a : Type) : Monad (func a) :=
  { bind := @func_bind a
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
