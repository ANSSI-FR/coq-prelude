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

From Coq Require Import FunctionalExtensionality Program.Basics.
From Prelude Require Import Classes Identity Equality.

Set Universe Polymorphism.

#[local]
Close Scope nat_scope.
#[local]
Open Scope prelude_scope.

(** * Definition *)

Definition state_t (s : Type) (m : Type -> Type) (a : Type) : Type :=
  s -> m (a * s).

Bind Scope monad_scope with state_t.

Definition run_state_t {m s a} (r : state_t s m a) (x : s) : m (a * s) :=
  r x.

Definition eval_state_t {m s a} `{Monad m} (r : state_t s m a) (x : s) : m a :=
  map fst (r x).

Definition exec_state_t {m s a} `{Monad m} (r : state_t s m a) (x : s) : m s :=
  map snd (r x).

(** * State Monad *)

Definition state_map {m s} `{Monad m} {a b} (f : a -> b) (r : state_t s m a)
  : state_t s m b :=
  fun* x => (fun o => (f (fst o), snd o)) <$> r x.

Lemma state_functor_identity {m s a} `{Monad m} `{Equality s} `{Equality a}
  (r : state_t s m a)
  : state_map id r == id r.

Proof.
  intros x.
  unfold state_map.
  rewrite bind_map.
  match goal with
  | |- context[bind _ ?f] =>
    assert (R: f == @pure m _ _);  [ now intros [y st] | rewrite R; clear R]
  end.
  apply bind_right_identity.
Qed.

Lemma state_functor_composition_identity {m s a b c} `{Monad m} `{Equality s} `{Equality c}
  (u : b -> c) (v : a -> b) (r : state_t s m a)
  : state_map (u <<< v) r == ((state_map u) <<< (state_map v)) r.

Proof.
  intros st.
  unfold state_map.
  change (fun o => ((u <<< v) (fst o), snd o))
    with ((fun o => (v (fst o), snd o)) >>> (fun o : b * s => (u (fst o), snd o))).
  apply functor_map_identity.
Qed.

#[program]
Instance state_Functor (m :  Type -> Type) `{Monad m} (s : Type) `{Equality s}
  : Functor (state_t s m) :=
  { map := @state_map m s _
  }.

Next Obligation.
  apply state_functor_identity.
Defined.

Next Obligation.
  apply state_functor_composition_identity.
Defined.

Definition state_apply {m s} `{Monad m} {a b}
  (f : state_t s m (a -> b)) (fs : state_t s m a)
  : state_t s m b :=
  fun* x => do
    let* u := f x in
    let* v := fs (snd u) in
    pure (fst u (fst v), snd v)
  end.

Definition state_pure {m s} `{Monad m} {a} (x : a) : state_t s m a :=
  fun* s => pure (x, s).

Lemma state_applicative_identity {m s} `{Monad m} `{Equality s} {a} `{Equality a}
  (v : state_t s m a):
  state_apply (state_pure id) v == v.

Proof.
  intros st.
  unfold state_apply.
  unfold state_pure.
  rewrite bind_left_identity.
  cbn.
  unfold id.
  match goal with |- context[bind _ ?f] => assert (R: f = fun v0 : a * s => pure v0) end;
  [| rewrite R; clear R]. {
    apply functional_extensionality.
    now intros [x st'].
  }
  apply bind_right_identity.
Qed.

Lemma state_applicative_homomorphism {m s} `{Monad m} `{Equality s} {a b} `{Equality b}
  (v : a -> b) (x : a)
  : state_apply (state_pure v) (state_pure x) == state_pure (m:=m) (s:=s) (v x).

Proof.
  cbn.
  intros st.
  unfold state_apply, state_pure.
  now repeat rewrite bind_left_identity.
Qed.

Lemma state_applicative_interchange {m s} `{Monad m} `{Equality s} {a b} `{Equality b}
  (u : state_t s m (a -> b)) (y : a)
  : state_apply u (state_pure y) == state_apply (state_pure (fun z : a -> b => z y)) u.

Proof.
  intro st.
  unfold state_apply, state_pure.
  rewrite bind_left_identity.
  cbn.
  match goal with
  | |- bind _ ?f == bind _ ?g =>
    assert (R : f == g); [| now rewrite R ]
  end.
  intros [f st'].
  now rewrite bind_left_identity.
Qed.

#[program]
Instance state_Applicative (m : Type -> Type) `{Monad m} (s : Type) `{Equality s}
  : Applicative (state_t s m) :=
  { pure := @state_pure m s _
  ; apply := @state_apply m s _
  }.

Next Obligation.
  apply state_applicative_identity.
Defined.

Next Obligation.
  unfold state_apply, state_pure.
  repeat rewrite bind_associativity.
  repeat rewrite bind_left_identity.
  repeat rewrite bind_associativity.
  cbn.
  match goal with
  | |- bind _ ?f == bind _ ?g => assert (R: f == g); [| now rewrite R ]
  end.
  intros [f st'].
  repeat rewrite bind_associativity.
  repeat rewrite bind_left_identity.
  repeat rewrite bind_associativity.
  cbn.
  match goal with
  | |- bind _ ?f == bind _ ?g => assert (R: f == g); [| now rewrite R ]
  end.
  intros [g st''].
  cbn.
  repeat rewrite bind_associativity.
  repeat rewrite bind_left_identity.
  cbn.
  match goal with
  | |- bind _ ?f == bind _ ?g => assert (R: f == g); [| now rewrite R ]
  end.
  intros [h st'''].
  cbn.
  unfold compose.
  repeat rewrite bind_left_identity.
  cbn.
  reflexivity.
Defined.

Next Obligation.
  apply state_applicative_homomorphism.
Defined.

Next Obligation.
  + apply state_applicative_interchange.
Defined.

Next Obligation.
  unfold state_map, state_pure, state_apply.
  rewrite bind_left_identity.
  cbn.
  now rewrite bind_map.
Qed.

Definition state_bind {m s} `{Monad m} {a b}
  (r : state_t s m a) (f : a -> state_t s m b)
  : state_t s m b :=
  fun* x => do
    let* u := r x in
    f (fst u) (snd u)
  end.

Lemma state_bind_associativity {m s} `{Monad m} `{Equality s} {a b c} `{Equality c}
  (f : state_t s m a) (g : a -> state_t s m b) (h : b -> state_t s m c)
  : state_bind (state_bind f g) h == state_bind f (fun x : a => state_bind (g x) h).
Proof.
  intros st.
  unfold state_bind.
  rewrite bind_associativity.
  reflexivity.
Qed.

#[program]
Instance state_Monad (m : Type -> Type) `{Monad m} (s : Type) `{Equality s}
  : Monad (state_t s m) :=
  { bind := @state_bind m s _
  }.

Next Obligation.
  unfold state_bind, state_pure.
  now rewrite bind_left_identity.
Defined.

Next Obligation.
  unfold state_bind, state_pure.
  assert (R: (fun u : a * s => pure (fst u, snd u)) == fun u : a * s => pure (f:=m) u)
    by  now intros [y st].
  rewrite R.
  now rewrite bind_right_identity.
Defined.

Next Obligation.
  apply state_bind_associativity.
Defined.

Next Obligation.
  unfold state_bind.
  match goal with
  | |- bind _ ?f == bind _ ?g =>
    assert (R: f == g); [ now intros | rewrite R; clear R ]
  end.
  reflexivity.
Defined.

Next Obligation.
  unfold state_map, state_bind.
  rewrite bind_map.
  reflexivity.
Defined.

(** * Transformer Instance *)

Definition state_lift {m s} `{Monad m} {a} (x : m a) : state_t s m a :=
  fun s => bind x (fun o => pure (o, s)).

Instance state_MonadTrans (s : Type) `{Equality s} : MonadTrans (state_t s) :=
  { lift := fun m H => @state_lift m s H
  }.

(** * State Instance *)

Definition state_get {m s} `{Monad m} : state_t s m s :=
  fun x => pure (x, x).

Definition state_put {m s} `{Monad m} (x : s) : state_t s m unit :=
  fun _ => pure (tt, x).

Instance state_StateMonad (m : Type -> Type) `{Monad m} (s : Type) `{Equality s}
  : MonadState s (state_t s m) :=
  { get := @state_get m s _
  ; put := @state_put m s _
  }.

(** * Pure Monad State *)

Definition state (s : Type) := state_t s id.
