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

From Coq Require Import Equivalence Setoid Morphisms.
From Prelude Require Export Equality.

Set Universe Polymorphism.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

#[local]
Open Scope prelude_scope.

Definition compose {a b c} (g : b -> c) (f : a -> b) : a -> c :=
  fun (x: a) => g (f x).

Definition id {a : Type} (x : a) : a := x.

Notation "f <<< g" := (compose f g) (at level 50) : function_scope.
Notation "f >>> g" := (compose g f) (at level 50) : function_scope.

Notation "'fun*' x .. z '=>' p" := (fun x => .. (fun z => p%monad) ..)
  (x binder, z binder, at level 200, only parsing) : function_scope.

Notation "f $ x" :=
  (f x) (only parsing, at level 99, right associativity) : prelude_scope.

(** * Functor *)

Class Functor (f : Type -> Type) : Type :=
  { functor_has_eq :> forall {a} `{Equality a}, Equality (f a)
  ; map {a b : Type} : (a -> b) -> f a -> f b
  ; functor_identity {a} `{Equality a} (x : f a) : map id x == id x
  ; functor_map_identity {a b c} `{Equality c} (u : b -> c) (v : a -> b) (x : f a)
    : map (u <<< v) x == map u (map v x)
  }.

Arguments map [f _ a b] (_ _%monad).
Arguments functor_identity [f _ a _] (x).
Arguments functor_map_identity [f _ a b c _] (u v x).

Definition fconst {f a b} `{Functor f} (x : a) (ft : f b) : f a :=
  map (fun _ => x) ft.

Arguments fconst [f a b _] x ft%monad.

Notation "f <$> g" := (map f g) (at level 27, left associativity) : monad_scope.
Notation "f <$ g" := (fconst f g) (at level 27, left associativity) : monad_scope.

#[local]
Open Scope monad_scope.

(** * Applicative *)

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) : Type :=
  { applicative_is_functor :> Functor f
  ; pure {a} : a -> f a
  ; apply {a b} : f (a -> b) -> f a -> f b
    where "f <*> g" := (apply f g)
  ; applicative_identity {a} `{Equality a} (v : f a) : pure id <*> v == v
  ; applicative_composition {a b c} `{Equality c} (u : f (b -> c)) (v : f (a -> b)) (w : f a)
    : pure compose <*> u <*> v <*> w == u <*> (v <*> w)
  ; applicative_homomorphism {a b} `{Equality b} (v : a -> b) (x : a)
    : (pure v) <*> (pure x) == pure (v x)
  ; applicative_interchange {a b} `{Equality b} (u : f (a -> b)) (y : a)
    : u <*> (pure y) == (pure (fun z => z y)) <*> u
  ; applicative_pure_map {a b} `{Equality b} (g : a -> b) (x : f a)
    : g <$> x == pure g <*> x
  }.

Arguments pure [f _ a] (x).
Arguments apply [f _ a b] (_%monad _%monad).
Arguments applicative_identity [f _ a _] (v).
Arguments applicative_composition [f _ a b c _] (u v w).
Arguments applicative_homomorphism [f _ a b _] (v x).
Arguments applicative_interchange [f _ a b _] (u y).
Arguments applicative_pure_map [f _ a b _] (g x).

Notation "f <*> g" := (apply f g) (at level 28, left associativity) : monad_scope.

Definition liftA2 {f a b c} `{Applicative f} (g : a -> b -> c) (x : f a) (y : f b) : f c :=
  apply (map g x) y.

Arguments liftA2 [f a b c _] (g x%monad y%monad).

Definition rseq {f a b} `{Applicative f} (x : f a) (y : f b) : f b :=
  (id <$ x) <*> y.

Arguments rseq [f a b _] (x%monad y%monad).

Notation "f *> g" := (rseq f g) (at level 28, left associativity) : monad_scope.

Definition lseq {f a b} `{Applicative f} (x : f a) (y : f b) : f a :=
  liftA2 (fun x _ => x) x y.

Arguments lseq [f a b _] (x%monad y%monad).

Notation "f <* g" := (lseq f g) (at level 28, left associativity) : monad_scope.

(** * Monad *)

Reserved Notation "f >>= g" (at level 20, left associativity).

Class Monad (m:  Type -> Type) :=
  { monad_is_apply :> Applicative m
  ; bind {a b} : m a -> (a -> m b) -> m b
    where "f >>= g" := (bind f g)
  ; bind_left_identity {a b} `{Equality b} (x : a) (f : a -> m b)
    : pure x >>= f == f x
  ; bind_right_identity {a} `{Equality a} (x : m a)
    : x >>= (fun y => pure y) == x
  ; bind_associativity {a b c} `{Equality c} (f : m a) (g : a -> m b) (h : b -> m c)
    : (f >>= g) >>= h == f >>= (fun x => (g x) >>= h)
  ; bind_morphism {a b} `{Equality b} (x : m a) (f f' : a -> m b)
    : f == f' -> bind x f == bind x f'
  ; bind_map {a b} `{Equality b} (x : m a) (f : a -> b)
    : f <$> x == (x >>= (fun y => pure (f y)))
  }.

Notation "f >>= g" := (bind f g) (at level 20, left associativity) : monad_scope.

Arguments bind [m _ a b] (f%monad g%monad).
Arguments bind_left_identity [m _ a b _] (x f).
Arguments bind_right_identity [m _ a _] (x).
Arguments bind_associativity [m _ a b c _] (f g h).
Arguments bind_morphism [m _ a b _] (x f f').
Arguments bind_map [m _ a b _] (x f).

#[local]
Open Scope signature_scope.

#[program]
Instance bind_Proper (m : Type -> Type) `{Monad m} (a b : Type) `{Equality b}
  : Proper (@eq (m a) ==> @equal (a -> m b) _ ==> @equal (m b) functor_has_eq) (@bind m _ _ _).

Next Obligation.
  add_morphism_tactic.
  intros x f g equ.
  apply bind_morphism.
  exact equ.
Qed.

Definition join {m a} `{Monad m} (x : m (m a)) : m a :=
  x >>= id.

Arguments join [m a _] (x%monad).

Definition void {m a} `{Monad m} (x : m a) : m unit :=
  x >>= fun _ => pure tt.

Arguments void [m a _] (x%monad).

Definition when {m a} `{Monad m} (cond : bool) (x : m a) : m unit :=
  if cond then void x else pure tt.

Arguments when [m a _] (cond x%monad).

Declare Custom Entry monad.

Notation "'do' p 'end'" := p (p custom monad at level 10) : prelude_scope.

Notation "p ';' q" := (bind p%monad (fun _ => q%monad))
  (in custom monad at level 10, q at level 10, right associativity, only parsing).

Notation "'let*' a '<-' p 'in' q" := (bind p%monad (fun a => q%monad))
  (in custom monad at level 0, a ident, p constr, q at level 10, right associativity, only parsing).

Notation "'let' a ':=' p 'in' q" := (let a := p in q%monad)
  (in custom monad at level 5, a ident, p constr, q at level 10, right associativity, only parsing).

Notation "x" := x%monad (in custom monad at level 0, x constr at level 200, only parsing).

#[local]
Definition test_monad_notation {m} `{Monad m}
  (compute : nat -> m nat) (p : m unit) (q : nat -> m bool) : nat -> m bool := fun* _ => do
    p >>= (fun _ => q 2%nat);
    p;
    let z := 3 in
    let* x <- id <$> compute 3 in
    let* y <- compute 4 in
    q (x + y + z)
  end.
