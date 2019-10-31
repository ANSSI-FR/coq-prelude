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

From Coq Require Export Byte RelationClasses.
From Prelude Require Import Init Control Option Equality.

Definition format_byte_aux (x : list byte)
  : option (byte * list byte) :=
  match x with
  | x5c :: x :: rst => match x with
                       | x00 => Some (x00, rst) (* \0 *)
                       | x6e => Some (x0a, rst) (* \n *)
                       | x72 => Some (x0d, rst) (* \r *)
                       | x74 => Some (x09, rst) (* \t *)
                       | x5c => Some (x5c, rst) (* \\ *)
                       | _ => None
                       end
  | x :: rst => Some (x, rst)
  | _ => None
  end.

Definition format_byte (x : list byte) : option byte := fst <$> format_byte_aux x.
Definition to_byte (x : byte) : byte := x.
String Notation byte format_byte to_byte : byte_scope.

Inductive bytes := wrap_bytes { unwrap_bytes : list byte }.

Register bytes as prelude.data.bytes.type.
Register wrap_bytes as prelude.data.bytes.wrap_bytes.

From Coq Require Import Program.

#[program]
Fixpoint format_bytes_aux (input : list byte) {measure (List.length input)} : option (list byte) :=
  match input with
  | [] => Some []
  | _ => match format_byte_aux input with
         | Some (x, rst) => cons x <$> format_bytes_aux rst
         | None => None
         end
  end.

Next Obligation.
  destruct input.
  + discriminate.
  + cbn in Heq_anonymous.
    destruct b; inversion Heq_anonymous; subst; auto with arith.
    destruct input; inversion Heq_anonymous; subst; auto with arith.
    destruct b; inversion Heq_anonymous; subst; auto with arith.
Defined.

Definition format_bytes (input : list byte) : option bytes := wrap_bytes <$> format_bytes_aux input.

Declare Scope bytes_scope.
Delimit Scope bytes_scope with bytes.
Bind Scope bytes_scope with bytes.

String Notation bytes format_bytes unwrap_bytes : bytes_scope.

Definition append (x y : bytes) :=
  wrap_bytes (List.app (unwrap_bytes x) (unwrap_bytes y)).

Infix "++" := append : bytes_scope.

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
