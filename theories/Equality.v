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

Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.

(** * Weaker Equality

    For a number of type, the Coq equality is too strong. Therefore,
    we introduce the idea of a _weaker equality_ one can use in place
    of the Leibniz equality used in Coq.

 *)

Class Equality
      (A: Type) :=
  { equal (a a': A): Prop
  ; rel:> Equivalence equal
  }.

Arguments equal [A _] (_ _).

Instance default_Equality
         (A: Type)
  : Equality A|999 :=
  { equal := eq }.

Infix "==" :=
  equal
    (at level 70, no associativity)
  : prelude_scope.

Notation "a /= b" :=
  (~ equal a b)
    (at level 70, no associativity)
  : prelude_scope.

#[local]
Open Scope prelude_scope.

Lemma not_equal_sym
      {A:    Type} `{Equality A}
      (x y:  A)
  : x /= y -> y /= x.
Proof.
  intros Hneq Heq.
  now symmetry in Heq.
Qed.

Instance not_equal_Symmetric (A: Type) `{Equality A}
  : Symmetric (fun x y => x /= y) :=
  not_equal_sym.

(** * Weaker Decidable Equality

    Sometimes, it is not enough to have an equality. Thus, we
    introduce the notion of weaker decidable equality. It comes in two
    “flavors”: one based on sumbool and one based on bool.

 *)

Class DecidableEquality
      (A:  Type) `{Equality A} :=
  { equal_dec (a a':  A)
    : {equal a a'} + {~ equal a a'}
  }.

Arguments equal_dec [A _ _] (_ _).

Infix "=?" :=
  equal_dec
    (at level 70, no associativity)
  : prelude_scope.

(** * Instances

    ** Tactics

 *)

(** We provide several tactics to easy the definition of [Equality]
    and [DecidableEquality] instances. *)

#[local]
Ltac gen_default_decidable_equality a :=
  match a with
  | (?a == ?b /\ ?c)
    => destruct (a =? b); [ gen_default_decidable_equality c
                          | now right
                          ]
  | ?a == ?b
    => destruct (a =? b); [ now left
                          | now right
                          ]
  | _
    => idtac
  end.

Ltac default_record_equality_instances :=
  repeat constructor;
    ( reflexivity
    + (now symmetry)
    + (repeat match goal with
              | [H: ?a /\ ?b |- _] => destruct H as [?A ?B]
              end;
       match goal with
       | [H1: ?a == ?b, H2: ?b == ?c |- ?a == ?c]
         => transitivity b; [exact H1 | exact H2]
       | [|- _]
         => idtac
       end)
    ).

Ltac default_decidable_equality :=
  match goal with
  | [|- { ?a } + { _ } ]
    => gen_default_decidable_equality a
  end.

(** ** Function Instances *)

#[program]
Instance function_Equality
         (a b:  Type)
        `{Equality b}
  : Equality (a -> b) :=
  { equal := fun f g => forall (x: a), f x == g x
  }.

Next Obligation.
  repeat constructor.
  + now intro x.
  + now intros x y.
  + intros x y z H1 H2 r.
    now etransitivity.
Defined.

(** ** Tuple Instances

 *)

#[program]
Instance tuple_Equality
         (a b:  Type) `{Equality a} `{Equality b}
  : Equality (a * b) :=
  { equal := fun o o' => fst o == fst o' /\ snd o == snd o'
  }.

Next Obligation.
  default_record_equality_instances.
Defined.

Add Parametric Morphism
    (a b:  Type) `{Equality a} `{Equality b}
  : fst
    with signature (@equal (a * b) _) ==> (@equal a _)
      as fst_tuple_equal_morphism.
Proof.
  intros o o' [P Q].
  exact P.
Qed.

Add Parametric Morphism
    (a b:  Type) `{Equality a} `{Equality b}
  : snd
    with signature (@equal (a * b) _) ==> (@equal b _)
      as snd_tuple_equal_morphism.
Proof.
  intros o o' [P Q].
  exact Q.
Qed.

Add Parametric Morphism
    (a b:  Type) `{Equality a} `{Equality b}
  : pair
    with signature (@equal a _) ==> (@equal b _) ==> (@equal (a * b) _)
      as pair_tuple_equal_morphism.
Proof.
  intros o o' Heq p p' Heq'.
  constructor; [ exact Heq
               | exact Heq'
               ].
Qed.

#[program]
Instance tuple_DecidableEquality
         (a b:  Type) `{DecidableEquality a} `{DecidableEquality b}
  : DecidableEquality (a * b).

Next Obligation.
  default_decidable_equality.
Defined.

(** ** Nat

 *)

#[program]
Instance nat_DecidableEquality
  : DecidableEquality nat.

Next Obligation.
  repeat decide equality.
Defined.

(** **

 *)

Require Import Coq.ZArith.ZArith.

#[program]
Instance Z_DecidableEquality
  : DecidableEquality Z.

Next Obligation.
  repeat decide equality.
Defined.

(** ** Bool

 *)

#[program]
Instance bool_DecidableEquality
 : DecidableEquality bool.

Next Obligation.
  repeat decide equality.
Defined.

(** ** Option

 *)

Inductive option_equal
          {a:    Type}
         `{Equality a}
  : option a -> option a -> Prop :=
| option_equal_some (x:    a)
                    (y:    a)
                    (Heq:  x == y)
  : option_equal (Some x) (Some y)
| option_equal_none
  : option_equal None None.

#[program]
Instance option_Equality
         (a:  Type) `{Equality a}
  : Equality (option a) :=
  { equal := option_equal
  }.

Next Obligation.
  repeat constructor.
  + intros [x|]; now constructor.
  + intros [x|] y Heq; inversion Heq; subst; now constructor.
  + intros x y z Heq Heq'.
    inversion Heq; subst;
      inversion Heq'; subst;
        constructor.
    now transitivity y0.
Defined.


Add Parametric Morphism
    (a:  Type) `{Equality a}
  : (@Some a)
    with signature (@equal a _) ==> (@equal (option a) _)
      as some_equal_morphism.
  + intros x y Heq.
    constructor.
    exact Heq.
Qed.

(** ** List

 *)

Inductive list_equal
          {a:  Type} `{Equality a}
  : list a -> list a -> Prop :=
| list_equal_cons (x y:   a)
                  (r r':  list a)
                  (Heq:   x == y)
                  (Heq':  list_equal r r')
  : list_equal (cons x r) (cons y r')
| list_equal_nil
  : list_equal nil nil.

#[program]
Instance list_Equality
         (a:  Type) `{Equality a}
  : Equality (list a) :=
  { equal := list_equal
  }.

Next Obligation.
  repeat constructor.
  + intros l; induction l; now constructor.
  + intros l; induction l; intros l' Heq; inversion Heq; constructor.
    ++ now subst.
    ++ now apply IHl.
  + intros l; induction l; intros l' l'' Heq Heq'; inversion Heq; subst; inversion Heq'; subst; constructor.
    ++ now transitivity y.
    ++ eapply IHl.
       exact Heq'0.
       exact Heq'1.
Defined.

#[program]
Fixpoint list_equal_dec
         {a: Type} `{DecidableEquality a}
         (l l':  list a)
  : { l == l' } + { l /= l' } :=
  match l, l' with
  | nil, nil
    => ltac:(left)
  | cons x rst, cons y rst'
    => if x =? y
       then if list_equal_dec rst rst'
            then ltac:(left)
            else ltac:(right)
       else ltac:(right)
  | cons _ _, nil
    => ltac:(right)
  | nil, cons _ _
    => ltac:(right)
  end.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  now constructor.
Defined.

Next Obligation.
  intros F.
  inversion F; now subst.
Defined.

Next Obligation.
  intros F.
  inversion F; now subst.
Defined.

Next Obligation.
  now intros F.
Defined.

Next Obligation.
  now intros F.
Defined.

#[program]
Instance list_DecidableEquality
         (a: Type) `{DecidableEquality a}
  : DecidableEquality (list a) :=
  { equal_dec := list_equal_dec
  }.

(** ** String

 *)

Instance string_EqualityDec
  : DecidableEquality string :=
  { equal_dec := string_dec
  }.

(** ** Sigma-type
 *)

#[program]
Instance sigma_Equality
         (T: Type) `{H: Equality T}
         (P: T -> Prop)
  : Equality { a: T | P a } :=
  { equal := fun x y => proj1_sig x == proj1_sig y
  }.

Next Obligation.
  default_record_equality_instances.
  now intro x.
  now intros x y.
  intros x y z Heq1 Heq2.
  now transitivity (proj1_sig y).
Defined.