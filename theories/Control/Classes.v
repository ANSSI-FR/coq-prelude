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

From Prelude Require Export Control Equality.

(** * Monad Transformer *)

Class MonadTrans (t : forall (m : Type -> Type), Type -> Type) : Type :=
  { monad_trans_is_monad (m : Type -> Type) `{Monad m} :> Monad (t m)
  ; lift {m} `{Monad m} (a : Type) : m a -> t m a
  }.

Arguments lift [t _ m _ a] (_%monad).

(** * State Monad *)

Class MonadState (s : Type) (m : Type -> Type) :=
  { monadstate_is_monad :> Monad m
  ; put : s -> m unit
  ; get : m s
  }.

Arguments put [s m _] _.
Arguments get {s m _}.

#[local]
Open Scope monad_scope.

Definition modify {s m} `{MonadState s m} (f : s -> s) : m unit :=
  get >>= fun x => put (f x).

Definition gets {s a m} `{MonadState s m} (f : s -> a) : m a :=
  get >>= fun x => pure (f x).

Instance monadtransform_state
  (t : forall (m : Type -> Type), Type -> Type) `{MonadTrans t}
  (s : Type) (m : Type -> Type) `{MonadState s m}
  : MonadState s (t m) :=
  { put := fun x => lift (put x)
  ; get := lift get
  }.

(** * Reader Monad *)

Class MonadReader (r : Type) (m : Type -> Type) : Type :=
  { monadreader_is_monad :> Monad m
  ; ask : m r
  }.

Arguments ask {r m _}.

Instance monadtransform_reader
  (t : forall (m: Type -> Type), Type -> Type) `{MonadTrans t}
  (r : Type) (m : Type -> Type) `{MonadReader r m}
  : MonadReader r (t m) :=
  { ask := lift ask
  }.
