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

#[local]
Open Scope prelude_scope.

Bind Scope monad_scope with option.

Inductive is_some {a}: option a -> Prop :=
| is_some_rule (x:  a): is_some (Some x).

#[program]
Definition is_some_dec {a} (x : option a) : { is_some x } + { ~ is_some x } :=
  match x with
  | Some x => left (is_some_rule x)
  | None => right _
  end.

Next Obligation.
  now intro H.
Defined.

#[program]
Instance option_Functor : Functor option :=
  { map := option_map
  }.

Next Obligation.
  destruct x.
  + now constructor.
  + constructor.
Defined.

Next Obligation.
  destruct x.
  + now constructor.
  + constructor.
Defined.

Definition option_app {a b} (f : option (a -> b)) (x : option a) : option b :=
  match f with
  | Some f => f <$> x
  | None => None
  end.

#[program]
Instance option_Applicative : Applicative option :=
  { apply := @option_app
  ; pure  := @Some
  }.

Next Obligation.
  destruct v; now constructor.
Defined.

Next Obligation.
  destruct w; destruct v; destruct u; now constructor.
Defined.

Next Obligation.
  now constructor.
Defined.

Next Obligation.
  destruct u; now constructor.
Defined.

Next Obligation.
  destruct x; now constructor.
Defined.

Definition option_bind {a b} (x : option a) (f : a -> option b) : option b :=
  match x with
  | Some x => f x
  | None => None
  end.

#[program]
Instance option_Monad
  : Monad option :=
  { bind := @option_bind
  }.

Next Obligation.
  destruct (f x); now constructor.
Defined.

Next Obligation.
  destruct x; now constructor.
Defined.

Next Obligation.
  destruct f; cbn; [| constructor ].
  destruct (g a0); cbn; [| constructor ].
  destruct (h b0); now constructor.
Defined.

Next Obligation.
  destruct x; [| constructor].
  apply H0.
Defined.

Next Obligation.
  destruct x; now constructor.
Defined.

Definition maybe {a b} (f : a -> b) (x : b) (o : option a) : b :=
  match o with
  | Some o => f o
  | None => x
  end.

Definition fromMaybe {a} (x : a) (o : option a) : a :=
  maybe id x o.
