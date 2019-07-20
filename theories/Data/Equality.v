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

From Coq Require Import Setoid PeanoNat String Int63.
From Prelude Require Import Init.

(** * Equality

    For a number of type, the Coq equality is too strong. Therefore,
    we introduce the idea of a _weaker equality_ one can use in place
    of the Leibniz equality used in Coq.

 *)

Class Equality (a : Type) :=
  { equal (x y : a) : Prop
  ; rel :> Equivalence equal
  }.

Arguments equal [a _] (_ _).

(* To be used with [Proper] *)
Notation "''equal'" := (@equal _ _) (only parsing) : prelude_scope.

Instance default_Equality (a : Type)
  : Equality a|999 :=
  { equal := eq
  }.

Infix "==" := equal (at level 70, no associativity) : prelude_scope.
Notation "x /= y" := (~ equal x y) (at level 70, no associativity) : prelude_scope.

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

Class EquDec (a : Type) `{Equality a} :=
  { equalb (x y : a) : bool
  ; equalb_equ_true (x y : a) : x == y <-> equalb x y = true
  }.

Infix "?=" := equalb (at level 70, no associativity) : prelude_scope.
Notation "x ?/= y" := (negb (x ?= y)) (at level 70, no associativity) : prelude_scope.

Lemma equalb_equ_false `{EquDec a} (x y : a) : x /= y <-> x ?/= y = true.

Proof.
  case_eq (x ?= y); intros equ; cbn.
  + rewrite <- equalb_equ_true in equ.
    split.
    ++ now intros equ'.
    ++ now intros.
  + split.
    ++ auto.
    ++ intros _.
       intros falso.
       rewrite equalb_equ_true in falso.
       now rewrite equ in falso.
Qed.

(** * Instances *)

(** ** Tactics *)

(** We provide several tactics to easy the definition of [Equality]
    and [DecidableEquality] instances. *)

#[local]
Ltac gen_default_decidable_equality a :=
  match a with
  | (?a == ?b /\ ?c)
    => destruct (a ?= b); [ gen_default_decidable_equality c
                          | now right
                          ]
  | ?a == ?b
    => destruct (a ?= b); [ now left
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
              | H: ?a /\ ?b |- _ => destruct H as [?A ?B]
              end;
       match goal with
       | [H1: ?a == ?b, H2: ?b == ?c |- ?a == ?c]
         => transitivity b; [exact H1 | exact H2]
       | |- _
         => idtac
       end)
    ).

Ltac default_decidable_equality :=
  match goal with
  | |- { ?a } + { _ }
    => gen_default_decidable_equality a
  end.

(** ** Function Instances *)

#[program]
Instance function_Equality {a} `{Equality b} : Equality (a -> b) :=
  { equal := fun f g => forall (x: a), f x == g x
  }.

Next Obligation.
  repeat constructor.
  + now intro x.
  + now intros x y.
  + intros x y z H1 H2 r.
    now etransitivity.
Defined.

(** ** Tuple Instances *)

#[program]
Instance tuple_Equality `{Equality a, Equality b} : Equality (a * b) :=
  { equal := fun o o' => fst o == fst o' /\ snd o == snd o'
  }.

Next Obligation.
  default_record_equality_instances.
Defined.

#[local] Open Scope signature_scope.
From Coq Require Import Morphisms.

Instance fst_tuple_equal_Proper `(Equality a, Equality b)
  : Proper ('equal ==> 'equal) (@fst a b).

Proof.
  add_morphism_tactic.
  intros o o' [P Q].
  exact P.
Qed.

Instance snd_tuple_equal_Proper `(Equality a, Equality b)
  : Proper ('equal ==> 'equal) (@snd a b).

Proof.
  add_morphism_tactic.
  intros o o' [P Q].
  exact Q.
Qed.

Instance pair_tuple_equal_Proper `(Equality a, Equality b)
  : Proper ('equal ==> 'equal ==> 'equal) (@pair a b).

Proof.
  add_morphism_tactic.
  intros o o' Heq p p' Heq'.
  constructor; [ exact Heq
               | exact Heq'
               ].
Qed.

Lemma equalb_false_equ `{EquDec a} (x y : a) : (x ?= y) = false <-> (x ?/= y) = true.

Proof.
  case_eq (x ?= y); intros equ; split; now intros.
Qed.

#[program]
Instance tuple_EquDec `{EquDec a, EquDec b} : EquDec (a * b) :=
  { equalb := fun x y => andb (fst x ?= fst y) (snd x ?= snd y)
  }.

Next Obligation.
  cbn.
  case_eq (a1 ?= a0); intros equ; case_eq (b1 ?= b0); intros equ'; cbn.
  + rewrite <- equalb_equ_true in equ.
    rewrite <- equalb_equ_true in equ'.
    now repeat split.
  + rewrite <- equalb_equ_true in equ.
    rewrite equalb_false_equ in equ'.
    rewrite <- equalb_equ_false in equ'.
    split.
    ++ now intros [_ falso].
    ++ now intros falso.
  + rewrite <- equalb_equ_true in equ'.
    rewrite equalb_false_equ in equ.
    rewrite <- equalb_equ_false in equ.
    split.
    ++ now intros [falso _].
    ++ now intros falso.
  + rewrite equalb_false_equ in equ.
    rewrite equalb_false_equ in equ'.
    rewrite <- equalb_equ_false in equ.
    rewrite <- equalb_equ_false in equ'.
    now repeat split.
Defined.

(** ** Nat *)

#[program]
Instance nat_EquDec : @EquDec nat _ :=
  { equalb := Nat.eqb
  }.

Next Obligation.
  now rewrite Nat.eqb_eq.
Defined.

(** ** Z *)

From Coq Require Import ZArith.

#[program]
Instance Z_EquDec : EquDec Z :=
  { equalb := Z.eqb
  }.

Next Obligation.
  now rewrite Z.eqb_eq.
Defined.

(** ** Bool *)

#[program]
Instance bool_EquDec : EquDec bool :=
  { equalb := Bool.eqb
  }.

Next Obligation.
  now rewrite Bool.eqb_true_iff.
Defined.

(** ** Option *)

Inductive option_equal  `{Equality a} : option a -> option a -> Prop :=
| option_equal_some (x y : a) (equ : x == y)
  : option_equal (Some x) (Some y)
| option_equal_none
  : option_equal None None.

#[program]
Instance option_Equality `(Equality a) : Equality (option a) :=
  { equal := option_equal
  }.

Next Obligation.
  repeat constructor.
  + intros [x | ]; now constructor.
  + intros [x | ] y Heq; inversion Heq; subst; now constructor.
  + intros x y z Heq Heq'.
    inversion Heq; subst;
      inversion Heq'; subst;
        constructor.
    now transitivity y0.
Defined.

Instance some_equal_Proper `(Equality a) : Proper ('equal ==> 'equal) (@Some a).

Proof.
  add_morphism_tactic.
  intros x y Heq.
  constructor.
  exact Heq.
Qed.

(** ** List *)

Inductive list_equal `{Equality a} : list a -> list a -> Prop :=
| list_equal_cons (x y : a) (r r' :  list a) (equ : x == y) (next : list_equal r r')
  : list_equal (x :: r) (y :: r')
| list_equal_nil
  : list_equal [] [].

#[program]
Instance list_Equality `(Equality a) : Equality (list a) :=
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
       exact next.
       exact next0.
Defined.

Fixpoint list_equal_dec `{EquDec a} (l l' : list a) : bool :=
  match l, l' with
  | [], [] => true
  | x :: rst, y :: rst'
    => andb (x ?= y) (list_equal_dec rst rst')
  | _ :: _, []
    => false
  | [], _ :: _
    => false
  end.

From Coq Require Import FunInd.
Functional Scheme list_equal_dec_ind := Induction for list_equal_dec Sort Type.

#[program]
Instance list_EquDec
         (a: Type) `{EquDec a}
  : EquDec (list a) :=
  { equalb := list_equal_dec
  }.

Next Obligation.
  functional induction (list_equal_dec x y).
  + repeat constructor.
  + split.
    ++ intros falso.
       inversion falso.
    ++ now intros.
  + split.
    ++ intros falso.
       inversion falso.
    ++ now intros.
  + split.
    ++ intros equ.
       inversion equ; subst.
       rewrite equalb_equ_true in equ0.
       rewrite equ0.
       now rewrite <- IHb.
    ++ intros equ.
       apply andb_prop in equ.
       destruct equ as [equ1 equ2].
       apply equalb_equ_true in equ1.
       rewrite <- IHb in equ2.
       now constructor.
Defined.

(** ** String *)

#[program]
Instance string_EquDec
  : EquDec string :=
  { equalb := String.eqb
  }.

Next Obligation.
  now rewrite String.eqb_eq.
Defined.

(** ** Sigma-type *)

#[program]
Instance sigma_Equality `(Equality T) (P : T -> Prop)
  : Equality { a: T | P a } :=
  { equal := fun x y => proj1_sig x == proj1_sig y
  }.

Next Obligation.
  default_record_equality_instances.
  + now intro x.
  + now intros x y.
  + intros x y z Heq1 Heq2.
    now transitivity (proj1_sig y).
Defined.

#[program]
Instance sigma_EquDec `(EquDec T) (P : T -> Prop)
  : EquDec { a: T | P a } :=
  { equalb := fun x y => proj1_sig x ?= proj1_sig y
  }.

Next Obligation.
  apply equalb_equ_true.
Defined.
