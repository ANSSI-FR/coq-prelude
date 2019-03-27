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

Instance option_Functor
  : Functor option :=
  { map := option_map
  }.
+ intros a Ha x.
  now induction x.
+ intros a b c Hc u v x.
  now induction x.
Defined.

Definition option_app
           (a b:  Type)
           (f:    option (a -> b))
           (x:    option a)
  : option b :=
  match f with
  | Some f
    => f <$> x
  | None
    => None
  end.

Instance option_Applicative
  : Applicative option :=
  { apply := option_app
  ; pure  := fun (a:  Type) => @Some a
  }.
+ intros a Heq x.
  now induction x.
+ intros a b c Hc u v w.
  now (induction w; induction v; induction u).
+ intros a b Hb v x.
  now constructor.
+ intros a b Hb u y.
  now destruct u.
+ intros a b Hb g x.
  now destruct x.
Defined.

Definition option_bind
           (a b:  Type)
           (x:    option a)
           (f:    a -> option b)
  : option b :=
  match x with
  | Some x
    => f x
  | None
    => None
  end.

Instance option_Monad
  : Monad option :=
  { bind := option_bind
  }.
+ now intros a b Hb x f.
+ intros a Ha x.
  now induction x.
+ intros a b c Hc f g h.
  now induction f.
+ intros a b Hb x f f' Heq.
  destruct x; [| constructor ].
  apply Heq.
+ intros a b Hb x f.
  now destruct x.
Defined.