(* coq-prelude
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Program.Equality.

Require Import Control.Either.
Require Import Data.Void.

Import ListNotations.
Local Open Scope list_scope.

(** If you use polymorphic definition, do no use function from the
    standard library. Define your own. *)
Polymorphic Fixpoint cardinal
            {a:  Type}
            (l:  list a)
  : nat :=
  match l with
  | _ :: rst
    => S (cardinal rst)
  | nil
    => O
  end.

Polymorphic Fixpoint get
            (set:  list Type)
            (n:    nat)
            {struct n}
  : Type :=
  match n, set with
  | 0, t :: _
    => t
  | S n, _ :: set'
    => get set' n
  | _, _
    => Void
  end.

(** The open [union] type. For instance, a value [(v: union [nat;
    bool])] will be either of type [nat] or [bool]. *)
Polymorphic Program Inductive union
            (set:  list Type)
  : Type :=
| OneOf {t:  Type}
        (n:  nat)
        (Ht: get set n = t)
        (Hn: n < cardinal set )
        (x:  t)
  : union set.

Arguments OneOf [set t] (n Ht Hn x).

(** An “open product”. Similarly to [union], it is parameterized by a
    list of types. *)
Polymorphic Inductive product
  : list Type -> Type :=
| Acons (a:    Type)
        (x:    a)
        (set:  list Type)
        (rst:  product set)
  : product (a :: set)
| Anil
  : product [].

Arguments Acons [a] (x) [set] (rst).

(** Given an open product [(x: product set)], get the [n]th element of
    type [get set n]. *)
Polymorphic Fixpoint fetch
            {set:  list Type}
            (x:    product set)
            (n:    nat)
            (H:    n < cardinal set)
  : get set n.
case_eq set.
+ intros Heq.
  subst.
  cbn in H.
  omega.
+ intros T l Heq.
  subst.
  dependent induction x.
  induction n.
  exact x.
  cbn.
  apply fetch.
  ++ exact x0.
  ++ cbn in H.
     omega.
Defined.

(** Given an open product [(x: product set)], change the [n]th element
    of type [get set n] by a new value [v]. *)
Polymorphic Fixpoint swap
            {set:  list Type}
            (x:    product set)
            (n:    nat)
            (H:    n < cardinal set)
            (v:    get set n)
            {struct x}
  : product set.
case_eq set.
+ intros Heq.
  subst.
  cbn in H.
  omega.
+ intros T l Heq.
  subst.
  dependent induction x.
  induction n.
  ++ exact (Acons v x0).
  ++ refine (Acons x _).
     apply (swap l x0 n).
     +++ cbn in H.
         omega.
     +++ exact v.
Defined.

(** Given a list of type [set] and a natural number [n], returns a
    list of type wherein the [n]th element of [set] is absent. *)
Polymorphic Fixpoint remove
            (set:  list Type)
            (n:    nat)
  : list Type :=
  match set, n with
  | _ :: rst, 0
    => rst
  | x :: rst, S n
    => x :: remove rst n
  | _, _
    => []
  end.


(** Given an arbitrary list of types [set], we want to be able to tell
    whether or not it contains the type [t]. This is what the
    [Contains] typeclass is for. *)
Polymorphic Class Contains
            (t:    Type)
            (set:  list Type)
  := { rank:            nat
     ; rank_get_t:      get set rank = t
     ; rank_bound:      rank < cardinal set
     }.

Arguments rank (t set) [_].
Arguments rank_get_t (t set) [_].
Arguments rank_bound (t set) [_].

(** One obvious instance of [Contains] is that the type [get set n] is
    contains in [set]. *)
Polymorphic Instance Contains_nat
            (set:  list Type)
            (n:    nat)
            (H:    n < cardinal set)
  : Contains (get set n) set :=
  { rank        := n
  ; rank_get_t  := eq_refl
  ; rank_bound  := H
  }.

(** Then, following what is often done in Haskell in this context, we
    can define two instances of [Contains]:

    First, a list contains its head. *)
Polymorphic Instance Contains_head
            (t:    Type)
            (set:  list Type)
  : Contains t (cons t set) :=
  { rank        := 0
  ; rank_get_t  := eq_refl
  }.
+ apply Nat.lt_0_succ.
Defined.

(** Then, if a list [set] contains a type [t], then any list
    constructed by appending an element to [set] also contains [t]. *)
Polymorphic Instance Contains_tail
            (t any:  Type)
            (set:    list Type)
            (H:      Contains t set)
  : Contains t (cons any set) :=
  { rank       := S (rank t set)
  }.
+ apply rank_get_t.
+ cbn.
  apply lt_n_S.
  apply rank_bound.
Defined.

(** Using the [Contains] typeclass, we can define a useful function
    [inj] to easily construct values of arbitrary open unions. *)
Polymorphic Program Definition inj
            {t:    Type}
            {set:  list Type} `{Contains t set}
            (x:    t)
  : union set :=
  OneOf (rank t set) (rank_get_t t set) (rank_bound t set) x.

(** The aim of the [visit] function is two fold. Given an open product
    [x] and a function [(f: t -> a * t)] such that a value of type [t]
    is present in [x] (as enforced by the [Contains] constraint). It
    returns the result of type [a] produced by [f] along with an open
    union such that the value of type [t] has been [swap]ped with the
    value of type [t] produced by [f]. *)
Definition visit
        {t:    Type}
        {set:  list Type} `{Contains t set}
        {a:    Type}
        (x:    product set)
        (f:    t -> a * t)
  : a * product set.
  refine (match fetch x (rank t set) (rank_bound t set)
                return get set (rank t set) = t -> a * product set
          with
          | v
            => fun (H: get set (rank t set) = t)
               => _
          end (rank_get_t t set)).
  remember (f (eq_rect (get set (rank t set)) (fun X => X) v t H)) as p.
  induction p as [v' u].
  refine (v', swap x (rank t set) (rank_bound t set) _).
  refine (eq_rect t (fun X => X) u (get set (rank t set)) _).
  symmetry.
  exact H.
Defined.