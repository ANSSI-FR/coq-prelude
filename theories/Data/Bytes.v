(* coq-prelude
 * Copyright (C) 2018–2019 ANSSI
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

From Coq Require Export Byte RelationClasses Int63.
From Prelude Require Import Init Byte Equality Control Option.

Inductive bytes := wrap_bytes { unwrap_bytes : list byte }.

Register bytes as prelude.data.bytes.type.
Register wrap_bytes as prelude.data.bytes.wrap_bytes.

Declare Scope bytes_scope.
Delimit Scope bytes_scope with bytes.
Bind Scope bytes_scope with bytes.

Definition append (x y : bytes) :=
  wrap_bytes (unwrap_bytes x ++ unwrap_bytes y).

Infix "++" := append : bytes_scope.

Definition length_nat (x : bytes) : nat :=
  List.length (unwrap_bytes x).

Definition length (x : bytes) : int :=
  let fix list_length (x : list byte) (acc : int) : int :=
      match x with
      | _ :: rst => list_length rst (acc + 1)%int63
      | [] => acc
      end
  in list_length (unwrap_bytes x) 0%int63.

Definition bytes_equal (x y : bytes) : Prop :=
  unwrap_bytes x == unwrap_bytes y.

#[program]
Instance bytes_equal_Equivalence : Equivalence bytes_equal.

Next Obligation.
  intros [x].
  cbn.
  induction x.
  + constructor.
  + now constructor.
Qed.

Next Obligation.
  intros [x] [y] equ.
  cbn in *.
  induction equ.
  + constructor.
    ++ now symmetry.
    ++ apply IHequ.
  + constructor.
Qed.

Next Obligation.
  intros [x] [y] [z] equ equ'.
  cbn in *.
  revert y z equ equ'.
  induction x; intros y z equ equ';
    inversion equ; subst; inversion equ'; subst; auto.
  constructor.
  + transitivity y0; auto.
  + eapply IHx; eauto.
Qed.

#[program]
Instance bytes_Equality : Equality bytes :=
  { equal := bytes_equal
  }.

#[program]
Instance bytes_EquDec : EquDec bytes :=
  { equalb := fun (x y : bytes) => unwrap_bytes x ?= unwrap_bytes y
  }.

Next Obligation.
  destruct x as [x]; destruct y as [y].
  cbn.
  split.
  + intros equ.
    assert (equ' : x == y) by apply equ.
    now rewrite equalb_equ_true in equ'.
  + intros equ.
    assert (equ' : x ?= y = true) by apply equ.
    now rewrite <- equalb_equ_true in equ'.
Qed.

#[local]
Fixpoint list_byte_of_list_byte_fmt (i : list byte) : option (list byte) :=
  match i with
  | c#"\" :: c#"0" :: rst => cons c#"\0" <$> list_byte_of_list_byte_fmt rst
  | c#"\" :: c#"n" :: rst => cons c#"\n" <$> list_byte_of_list_byte_fmt rst
  | c#"\" :: c#"r" :: rst => cons c#"\r" <$> list_byte_of_list_byte_fmt rst
  | c#"\" :: c#"t" :: rst => cons c#"\t" <$> list_byte_of_list_byte_fmt rst
  | c#"\" :: c#"\" :: rst => cons c#"\"  <$> list_byte_of_list_byte_fmt rst
  | c#"\" :: _     :: rst => None
  | x     :: rst          => cons x <$> list_byte_of_list_byte_fmt rst
  | [] => Some []
  end.

#[local]
Fixpoint bytes_of_list_byte_fmt (i : list byte) : option bytes :=
  wrap_bytes <$> list_byte_of_list_byte_fmt i.

String Notation bytes bytes_of_list_byte_fmt unwrap_bytes : bytes_scope.
Notation "'b#' c" := (c%bytes) (at level 0, c constr, no associativity, only parsing) : prelude_scope.
