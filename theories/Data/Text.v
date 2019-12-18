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

From Coq Require Import RelationClasses Program Int63 FunInd.
From Prelude Require Import Init Control Option Equality Byte Bytes.

#[local] Open Scope bool_scope.

(** * UTF-8 Wide Characters *)

Inductive wchar : Type :=
| wchar_var_1 : byte -> wchar
| wchar_var_2 : byte -> byte -> wchar
| wchar_var_3 : byte -> byte -> byte -> wchar
| wchar_var_4 : byte -> byte -> byte -> byte -> wchar.

Declare Scope wchar_scope.
Delimit Scope wchar_scope with wchar.
Bind Scope wchar_scope with wchar.

Definition wchar_size_nat (x : wchar) : nat :=
  match x with
  | wchar_var_1 x => 1
  | wchar_var_2 x y => 2
  | wchar_var_3 x y z => 3
  | wchar_var_4 x y z r => 4
  end.

Definition wchar_size (x : wchar) : int :=
  match x with
  | wchar_var_1 x => 1
  | wchar_var_2 x y => 2
  | wchar_var_3 x y z => 3
  | wchar_var_4 x y z r => 4
  end.

Definition wchar_eqb (c c' : wchar) : bool :=
  match c, c' with
  | wchar_var_1 x, wchar_var_1 x' => Byte.eqb x x'
  | wchar_var_2 x y, wchar_var_2 x' y' => Byte.eqb x x' && Byte.eqb y y'
  | wchar_var_3 x y z, wchar_var_3 x' y' z' => Byte.eqb x x' && Byte.eqb y y' && Byte.eqb z z'
  | wchar_var_4 x y z r, wchar_var_4 x' y' z' r' =>
    Byte.eqb x x' && Byte.eqb y y' && Byte.eqb z z' && Byte.eqb r r'
  | _, _ => false
  end.

#[program]
 Instance wchar_EquDec : EquDec wchar :=
  { equalb := wchar_eqb
  }.

Next Obligation.
  split.
  + intros equ.
    subst.
    destruct y;
      repeat (apply andb_true_intro; split);
      now apply Byte.byte_dec_lb.
  + intros equ.
    destruct x; destruct y; try discriminate; cbn in *;
      repeat match goal with
             | H : andb _ _ = true |- _ =>
               apply andb_prop in H; destruct H
             | H : Byte.eqb _ _ = true |- _ => apply Byte.byte_dec_bl in H; subst
             end;
      reflexivity.
Qed.

#[local]
Definition list_byte_of_wchar (c : wchar) : list byte :=
  match c with
  | wchar_var_1 x => [x]
  | wchar_var_2 x y => [x; y]
  | wchar_var_3 x y z  => [x; y; z]
  | wchar_var_4 x y z r => [x; y; z; r]
  end.

Definition bytes_of_wchar (c : wchar) : bytes :=
  wrap_bytes (list_byte_of_wchar c).

#[local]
Definition read_wchar (l : list byte) : option (wchar * list byte) :=
  match l with
  | x :: rst => if leb (int_of_byte x) 127 (* variant 1 *)
                then Some (wchar_var_1 x, rst)
                else if leb (int_of_byte x) 223 (* variant 2 *)
                then match rst with
                     | y :: rst =>
                       if leb (int_of_byte y) 191
                       then Some (wchar_var_2 x y, rst)
                       else None
                     | [] => None
                     end
                else if leb (int_of_byte x) 239 (* variant 3 *)
                then match rst with
                     | y :: z :: rst =>
                       if leb (int_of_byte y) 191 && leb (int_of_byte z) 191
                       then Some (wchar_var_3 x y z, rst)
                       else None
                     | _ => None
                     end
                else if leb (int_of_byte x) 247 (* variant 4 *)
                then match rst with
                     | y :: z :: r :: rst =>
                       if leb (int_of_byte y) 191 &&
                              leb (int_of_byte z) 191 &&
                              leb (int_of_byte r) 191
                       then Some (wchar_var_4 x y z r, rst)
                       else None
                     | _ => None
                     end
                     else None
  | _ => None
  end.

Functional Scheme read_wchar_ind := Induction for read_wchar Sort Type.

#[local]
Definition wchar_of_list_byte (l : list byte) : option wchar :=
    match read_wchar l with
    | Some (x, []) => Some x
    | _ => None
    end.

#[local]
Definition wchar_of_bytes (l : bytes) : option wchar :=
  wchar_of_list_byte (unwrap_bytes l).

(** * UTF-8 Strings *)

Inductive text :=
| TCons (c : wchar) (r : text) : text
| TNil : text.

Declare Scope text_scope.
Delimit Scope text_scope with text.
Bind Scope text_scope with text.

#[program, local]
Fixpoint text_of_list_byte (input : list byte) {measure (List.length input)} : option text :=
  match input with
  | [] => Some TNil
  | _ => match read_wchar input with
         | Some (x, rst) => TCons x <$> text_of_list_byte rst
         | None => None
         end
  end.

Next Obligation.
  functional induction (read_wchar input);
    try discriminate;
    inversion Heq_anonymous;
    subst;
    cbn;
    auto with arith.
Defined.

Fixpoint text_of_bytes (input : bytes) : option text :=
  text_of_list_byte (unwrap_bytes input).

#[local]
Fixpoint list_byte_of_text (t : text) : list byte :=
  match t with
  | TCons c r => List.app (list_byte_of_wchar c) (list_byte_of_text r)
  | TNil => []
  end.

Definition bytes_of_text (t : text) : bytes :=
  wrap_bytes (list_byte_of_text t).

Fixpoint append (x y : text) : text :=
  match x with
  | TCons x r => TCons x (append r y)
  | TNil => y
  end.

Infix "++" := append : text_scope.

Inductive text_equal : text -> text -> Prop :=
| text_equal_tcons (c : wchar) (r r' : text) (rec : text_equal r r')
  : text_equal (TCons c r) (TCons c r')
| text_equal_tnil
  : text_equal TNil TNil.

#[program]
Instance text_equal_Equivalence : Equivalence text_equal.

Next Obligation.
  intros t.
  induction t; now constructor.
Qed.

Next Obligation.
  intros x y equ.
  induction equ; now constructor.
Qed.

Next Obligation.
  intros x.
  induction x; intros y z equ equ';
    inversion equ; subst;
      inversion equ'; subst;
        constructor.
  eapply IHx; eassumption.
Qed.

#[program]
 Instance text_Equality : Equality text :=
  { equal := text_equal
  }.

Fixpoint text_eqb (t t' : text) : bool :=
  match t, t' with
  | TCons x r, TCons x' r' => (x ?= x') && text_eqb r r'
  | TNil, TNil => true
  | _, _ => false
  end.

#[program]
 Instance text_EquDec : EquDec text :=
  { equalb := text_eqb
  }.

Next Obligation.
  split.
  + intros equ.
    induction equ; subst.
    ++ cbn -[equalb].
       apply andb_true_intro.
       split.
       +++ apply equalb_equ_true.
           reflexivity.
       +++ apply IHequ.
    ++ reflexivity.
  + revert y.
    induction x; intros y equ; destruct y; try discriminate.
    ++ cbn -[equalb] in *.
       apply andb_prop in equ; destruct equ as [equ1 equ2].
       apply equalb_equ_true in equ1.
       cbn in equ1; subst.
       constructor.
       now apply IHx.
    ++ reflexivity.
Qed.

Fixpoint text_size_nat (t : text) : nat :=
  match t with
  | TCons x r => wchar_size_nat x + text_size_nat r
  | TNil => 0
  end.

Fixpoint text_size (t : text) : int :=
  let fix text_size_aux t (acc : int) :=
      match t with
      | TCons x r => text_size_aux r (add acc (wchar_size x))
      | TNil => acc
      end
  in text_size_aux t 0%int63.

Fixpoint text_length_nat (t : text) : nat :=
  match t with
  | TCons _ r => S (text_length_nat r)
  | _ => O
  end.

Fixpoint text_length (t : text) : int :=
  let fix text_length_aux t acc :=
      match t with
      | TCons _ r => text_length_aux r (add 1%int63 acc)
      | _ => 0%int63
      end
  in text_length_aux t 0%int63.

#[local]
Definition wchar_of_list_byte_fmt (x : list byte) : option wchar :=
  match text_of_list_byte x with
  | Some (TCons (wchar_var_1 "\") (TCons (wchar_var_1 "0") TNil)) => Some (wchar_var_1 x00) (* \0 *)
  | Some (TCons (wchar_var_1 "\") (TCons (wchar_var_1 "n") TNil)) => Some (wchar_var_1 x0a) (* \n *)
  | Some (TCons (wchar_var_1 "\") (TCons (wchar_var_1 "r") TNil)) => Some (wchar_var_1 x0d) (* \r *)
  | Some (TCons (wchar_var_1 "\") (TCons (wchar_var_1 "t") TNil)) => Some (wchar_var_1 x09) (* \t *)
  | Some (TCons x TNil) => Some x
  | _ => None
  end.

String Notation wchar wchar_of_list_byte_fmt list_byte_of_wchar : wchar_scope.
Notation "'w#' c" := (c%wchar) (at level 0, c constr, no associativity, only parsing) : prelude_scope.

Fixpoint text_of_text_fmt (x : text) : option text :=
  match x with
  | TCons "\" (TCons "n" rst) => TCons "\n" <$> (text_of_text_fmt rst)
  | TCons "\" (TCons "r" rst) => TCons "\r" <$> (text_of_text_fmt rst)
  | TCons "\" (TCons "t" rst) => TCons "\t" <$> (text_of_text_fmt rst)
  | TCons "\" (TCons "0" rst) => TCons "\0" <$> (text_of_text_fmt rst)
  | TCons "\" (TCons "\" rst) => TCons "\" <$> (text_of_text_fmt rst)
  | TCons "\" _ => None
  | TCons x rst => TCons x <$> text_of_text_fmt rst
  | TNil => Some TNil
  end.

Definition text_of_list_byte_fmt (x : list byte) : option text :=
  text_of_list_byte x >>= text_of_text_fmt.

String Notation text text_of_list_byte_fmt list_byte_of_text : text_scope.
Notation "'t#' c" := (c%text)  (at level 0, c constr, no associativity, only parsing) : prelude_scope.
