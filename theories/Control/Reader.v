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

Set Universe Polymorphism.

From Prelude Require Import Control.Classes Identity Equality.

#[local]
Open Scope prelude_scope.

(** * Definition *)

Definition reader_t (r : Type) (m : Type -> Type) (a : Type) : Type :=
  r -> m a.

Bind Scope monad_scope with reader_t.
Bind Scope function_scope with reader_t.

(** * Functor *)

Definition reader_map {m r} `{Monad m} {a b} (f : a -> b) (rd : reader_t r m a)
  : reader_t r m b :=
  fun* x => f <$> (rd x).

#[program]
Instance reader_Functor (m : Type -> Type) `{Monad m} (r : Type)
  : Functor (reader_t r m) :=
  { map := @reader_map m r _
  }.

Next Obligation.
  unfold reader_map.
  apply functor_identity.
Defined.

Next Obligation.
  unfold reader_map.
  apply functor_map_identity.
Defined.

(** * Applicative *)

Definition reader_pure {m r} `{Monad m} {a} (x : a)
  : reader_t r m a :=
  fun _ => pure x.

Definition reader_apply {m r} `{Monad m} {a b}
  (rf : reader_t r m (a -> b)) (rx : reader_t r m a)
  : reader_t r m b :=
  fun* r => rf r <*> rx r.

#[program]
Instance reader_Applicative (m : Type -> Type) `{Monad m} (r : Type)
  : Applicative (reader_t r m) :=
  { pure  := @reader_pure m r _
  ; apply := @reader_apply m r _
  }.

Next Obligation.
  unfold reader_apply.
  apply applicative_identity.
Defined.

Next Obligation.
  unfold reader_apply, reader_pure.
  apply applicative_composition.
Defined.

Next Obligation.
  unfold reader_apply, reader_pure.
  apply applicative_homomorphism.
Defined.

Next Obligation.
  unfold reader_apply, reader_pure.
  apply applicative_interchange.
Defined.

Next Obligation.
  unfold reader_map, reader_apply, reader_pure.
  apply applicative_pure_map.
Defined.

(** * Monad *)

Definition reader_bind {m r} `{Monad m} {a b}
  (p : reader_t r m a) (f : a -> reader_t r m b)
  : reader_t r m b :=
  fun* x => p x >>= fun y => f y x.

#[program]
Instance reader_Monad (m : Type -> Type) `{Monad m} (r : Type)
  : Monad (reader_t r m) :=
  { bind := @reader_bind m r _
  }.

Next Obligation.
  unfold reader_bind, reader_pure.
  apply bind_left_identity.
Defined.

Next Obligation.
  unfold reader_bind, reader_pure.
  apply bind_right_identity.
Defined.

Next Obligation.
  unfold reader_bind, reader_pure.
  apply bind_associativity.
Defined.

Next Obligation.
  unfold reader_bind, reader_pure.
  apply bind_morphism.
  intros z.
  apply H1.
Defined.

Next Obligation.
  unfold reader_map, reader_bind, reader_pure.
  apply bind_map.
Defined.

(** * Reader Monad *)

Instance reader_MonadReader (m : Type -> Type) `{Monad m} (r : Type)
  : MonadReader r (reader_t r m) :=
  { ask := fun x => pure x
  }.

(** * Pure Reader *)

Definition reader r x := reader_t r id x.
