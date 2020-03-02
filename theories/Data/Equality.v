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

From Coq Require Import Setoid PeanoNat String Int63 Byte.
From Prelude Require Import Init.

(** * Equality

    For a number of type, the Coq equality is too strong. Therefore,
    we introduce the idea of a _weaker equality_ one can use in place
    of the Leibniz equality used in Coq. *)

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

(** ** Byte *)

Definition byte_equb (x y : byte) : bool :=
  match x, y with
  | x00, x00 => true
  | x01, x01 => true
  | x02, x02 => true
  | x03, x03 => true
  | x04, x04 => true
  | x05, x05 => true
  | x06, x06 => true
  | x07, x07 => true
  | x08, x08 => true
  | x09, x09 => true
  | x0a, x0a => true
  | x0b, x0b => true
  | x0c, x0c => true
  | x0d, x0d => true
  | x0e, x0e => true
  | x0f, x0f => true
  | x10, x10 => true
  | x11, x11 => true
  | x12, x12 => true
  | x13, x13 => true
  | x14, x14 => true
  | x15, x15 => true
  | x16, x16 => true
  | x17, x17 => true
  | x18, x18 => true
  | x19, x19 => true
  | x1a, x1a => true
  | x1b, x1b => true
  | x1c, x1c => true
  | x1d, x1d => true
  | x1e, x1e => true
  | x1f, x1f => true
  | x20, x20 => true
  | x21, x21 => true
  | x22, x22 => true
  | x23, x23 => true
  | x24, x24 => true
  | x25, x25 => true
  | x26, x26 => true
  | x27, x27 => true
  | x28, x28 => true
  | x29, x29 => true
  | x2a, x2a => true
  | x2b, x2b => true
  | x2c, x2c => true
  | x2d, x2d => true
  | x2e, x2e => true
  | x2f, x2f => true
  | x30, x30 => true
  | x31, x31 => true
  | x32, x32 => true
  | x33, x33 => true
  | x34, x34 => true
  | x35, x35 => true
  | x36, x36 => true
  | x37, x37 => true
  | x38, x38 => true
  | x39, x39 => true
  | x3a, x3a => true
  | x3b, x3b => true
  | x3c, x3c => true
  | x3d, x3d => true
  | x3e, x3e => true
  | x3f, x3f => true
  | x40, x40 => true
  | x41, x41 => true
  | x42, x42 => true
  | x43, x43 => true
  | x44, x44 => true
  | x45, x45 => true
  | x46, x46 => true
  | x47, x47 => true
  | x48, x48 => true
  | x49, x49 => true
  | x4a, x4a => true
  | x4b, x4b => true
  | x4c, x4c => true
  | x4d, x4d => true
  | x4e, x4e => true
  | x4f, x4f => true
  | x50, x50 => true
  | x51, x51 => true
  | x52, x52 => true
  | x53, x53 => true
  | x54, x54 => true
  | x55, x55 => true
  | x56, x56 => true
  | x57, x57 => true
  | x58, x58 => true
  | x59, x59 => true
  | x5a, x5a => true
  | x5b, x5b => true
  | x5c, x5c => true
  | x5d, x5d => true
  | x5e, x5e => true
  | x5f, x5f => true
  | x60, x60 => true
  | x61, x61 => true
  | x62, x62 => true
  | x63, x63 => true
  | x64, x64 => true
  | x65, x65 => true
  | x66, x66 => true
  | x67, x67 => true
  | x68, x68 => true
  | x69, x69 => true
  | x6a, x6a => true
  | x6b, x6b => true
  | x6c, x6c => true
  | x6d, x6d => true
  | x6e, x6e => true
  | x6f, x6f => true
  | x70, x70 => true
  | x71, x71 => true
  | x72, x72 => true
  | x73, x73 => true
  | x74, x74 => true
  | x75, x75 => true
  | x76, x76 => true
  | x77, x77 => true
  | x78, x78 => true
  | x79, x79 => true
  | x7a, x7a => true
  | x7b, x7b => true
  | x7c, x7c => true
  | x7d, x7d => true
  | x7e, x7e => true
  | x7f, x7f => true
  | x80, x80 => true
  | x81, x81 => true
  | x82, x82 => true
  | x83, x83 => true
  | x84, x84 => true
  | x85, x85 => true
  | x86, x86 => true
  | x87, x87 => true
  | x88, x88 => true
  | x89, x89 => true
  | x8a, x8a => true
  | x8b, x8b => true
  | x8c, x8c => true
  | x8d, x8d => true
  | x8e, x8e => true
  | x8f, x8f => true
  | x90, x90 => true
  | x91, x91 => true
  | x92, x92 => true
  | x93, x93 => true
  | x94, x94 => true
  | x95, x95 => true
  | x96, x96 => true
  | x97, x97 => true
  | x98, x98 => true
  | x99, x99 => true
  | x9a, x9a => true
  | x9b, x9b => true
  | x9c, x9c => true
  | x9d, x9d => true
  | x9e, x9e => true
  | x9f, x9f => true
  | xa0, xa0 => true
  | xa1, xa1 => true
  | xa2, xa2 => true
  | xa3, xa3 => true
  | xa4, xa4 => true
  | xa5, xa5 => true
  | xa6, xa6 => true
  | xa7, xa7 => true
  | xa8, xa8 => true
  | xa9, xa9 => true
  | xaa, xaa => true
  | xab, xab => true
  | xac, xac => true
  | xad, xad => true
  | xae, xae => true
  | xaf, xaf => true
  | xb0, xb0 => true
  | xb1, xb1 => true
  | xb2, xb2 => true
  | xb3, xb3 => true
  | xb4, xb4 => true
  | xb5, xb5 => true
  | xb6, xb6 => true
  | xb7, xb7 => true
  | xb8, xb8 => true
  | xb9, xb9 => true
  | xba, xba => true
  | xbb, xbb => true
  | xbc, xbc => true
  | xbd, xbd => true
  | xbe, xbe => true
  | xbf, xbf => true
  | xc0, xc0 => true
  | xc1, xc1 => true
  | xc2, xc2 => true
  | xc3, xc3 => true
  | xc4, xc4 => true
  | xc5, xc5 => true
  | xc6, xc6 => true
  | xc7, xc7 => true
  | xc8, xc8 => true
  | xc9, xc9 => true
  | xca, xca => true
  | xcb, xcb => true
  | xcc, xcc => true
  | xcd, xcd => true
  | xce, xce => true
  | xcf, xcf => true
  | xd0, xd0 => true
  | xd1, xd1 => true
  | xd2, xd2 => true
  | xd3, xd3 => true
  | xd4, xd4 => true
  | xd5, xd5 => true
  | xd6, xd6 => true
  | xd7, xd7 => true
  | xd8, xd8 => true
  | xd9, xd9 => true
  | xda, xda => true
  | xdb, xdb => true
  | xdc, xdc => true
  | xdd, xdd => true
  | xde, xde => true
  | xdf, xdf => true
  | xe0, xe0 => true
  | xe1, xe1 => true
  | xe2, xe2 => true
  | xe3, xe3 => true
  | xe4, xe4 => true
  | xe5, xe5 => true
  | xe6, xe6 => true
  | xe7, xe7 => true
  | xe8, xe8 => true
  | xe9, xe9 => true
  | xea, xea => true
  | xeb, xeb => true
  | xec, xec => true
  | xed, xed => true
  | xee, xee => true
  | xef, xef => true
  | xf0, xf0 => true
  | xf1, xf1 => true
  | xf2, xf2 => true
  | xf3, xf3 => true
  | xf4, xf4 => true
  | xf5, xf5 => true
  | xf6, xf6 => true
  | xf7, xf7 => true
  | xf8, xf8 => true
  | xf9, xf9 => true
  | xfa, xfa => true
  | xfb, xfb => true
  | xfc, xfc => true
  | xfd, xfd => true
  | xfe, xfe => true
  | xff, xff => true
  | _, _ => false
  end.

Axiom byte_equb_correct : forall x y : byte, x = y <-> byte_equb x y = true.

#[program]
 Instance byte_EquDec : EquDec byte :=
  { equalb := byte_equb
  }.

Next Obligation.
  apply byte_equb_correct.
Defined.

(** ** Int *)

#[program]
 Instance int_EquDec : EquDec int :=
  { equalb := Int63.eqb
  }.

Next Obligation.
  now rewrite eqb_spec.
Defined.
