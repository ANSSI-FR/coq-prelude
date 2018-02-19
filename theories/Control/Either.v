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

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.

Require Import Prelude.Control.
Require Import Prelude.Control.Function.
Require Import Prelude.Equality.

Local Open Scope prelude_scope.

Inductive Either
          (L R:  Type)
  : Type :=
| Left (x:  L)
  : Either L R
| Right (y:  R)
  : Either L R.

Arguments Left [L R] (x).
Arguments Right [L R] (y).

Inductive either_equal
          {L R:  Type} `{Equality L} `{Equality R}
  : Either L R -> Either L R -> Prop :=
| equal_left (x y:  L)
           (Heq:  x == y)
  : either_equal (Left x) (Left y)
| equal_right (x y:  R)
            (Heq:  x == y)
  : either_equal (Right x) (Right y).

Fact either_equal_refl
     {L R:  Type} `{Equality L} `{Equality R}
     (x:    Either L R)
  : either_equal x x.
Proof.
  induction x;
    constructor;
    reflexivity.
Qed.

Fact either_equal_sym
     {L R:  Type} `{Equality L} `{Equality R}
     (x y:  Either L R)
  : either_equal x y
    -> either_equal y x.
Proof.
  intros Heq;
    destruct Heq as [x y Heq|x y Heq];
    symmetry in Heq;
    constructor;
    exact Heq.
Qed.

Fact either_equal_trans
     {L R:    Type} `{Equality L} `{Equality R}
     (x y z:  Either L R)
  : either_equal x y
    -> either_equal y z
    -> either_equal x z.
Proof.
  intros Heq1 Heq2.
  dependent induction Heq1;
    dependent induction Heq2;
    constructor;
    transitivity y;
    assumption.
  Qed.

Add Parametric Relation
    (L R:  Type) `{Equality L} `{Equality R}
  : (Either L R) either_equal
    reflexivity proved   by either_equal_refl
    symmetry proved      by either_equal_sym
    transitivity proved  by either_equal_trans
      as either_relation.

Instance either_Equal
         (L R:  Type) `{Equality L} `{Equality R}
  : Equality (Either L R) | 1 :=
  { equal := either_equal
  }.

Definition either_map
           (L A B:  Type)
           (f:      A -> B)
           (x:      Either L A)
  : Either L B :=
  match x with
  | Right x
    => Right (f x)
  | Left x
    => Left x
  end.

Instance either_Functor
         (L:  Type) `{Equality L}
  : Functor (Either L) :=
  { map := @either_map L
  }.
Proof.
+ intros A Ha x.
  induction x; reflexivity.
+ intros A B C Hc u v x.
  induction x; reflexivity.
Defined.

Definition either_pure
           (L A:  Type)
           (x:    A)
  : Either L A :=
  Right x.

Definition either_app
           (L A B:  Type)
           (fe:     Either L (A -> B))
           (x:      Either L A)
  : Either L B :=
  match fe, x with
  | Right f, Right x
    => Right (f x)
  | Left e, _ | _, Left e
    => Left e
  end.

Instance either_Applicative
         (L:  Type) `{Equality L}
  : Applicative (Either L) :=
  { pure  := @either_pure L
  ; apply := @either_app L
  }.
Proof.
  + intros A Ha x.
    induction x; reflexivity.
  + intros A B C Hc u v w.
    induction u; induction v; induction w; reflexivity.
  + intros A B Ha v x.
    reflexivity.
  + intros A B Hb u y.
    induction u; reflexivity.
  + intros A B Hb g [x|x]; reflexivity.
Defined.

Definition either_bind
           (L A B:  Type)
           (x:      Either L A)
           (f:      A -> Either L B)
  : Either L B :=
  match x with
  | Right x
    => f x
  | Left x
    => Left x
  end.

Instance either_Monad
         (L:  Type) `{Equality L}
  : Monad (Either L) :=
  { bind := either_bind L
  }.
Proof.
  + intros A B Hb x f; reflexivity.
  + intros A Ha [x|x]; reflexivity.
  + intros A B C Hc [f|f] g h; reflexivity.
  + intros A B Hb [x|x] f f' Heq.
    ++ reflexivity.
    ++ cbn.
       apply Heq.
  + intros A B Hb [x|x] f; reflexivity.
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