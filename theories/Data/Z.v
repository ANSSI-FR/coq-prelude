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

Require Import Coq.Program.Wf.
Require Import Coq.Program.Utils.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.PArith.Pnat.
Require Import Lia.

Local Open Scope char_scope.

Require Import Coq.ZArith.ZArith.

#[local]
Open Scope Z_scope.
#[local]
Open Scope program_scope.

#[program]
Definition ascii_of_Z
           (n: Z | 0 <= n < 10)
  : ascii :=
  match n mod 10 with
  | 0 =>  "0"
  | 1 =>  "1"
  | 2 =>  "2"
  | 3 =>  "3"
  | 4 =>  "4"
  | 5 =>  "5"
  | 6 =>  "6"
  | 7 =>  "7"
  | 8 =>  "8"
  | 9 =>  "9"
  | _ =>  "!" (* to be replaced by ! *)
  end.

Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Defined.
Next Obligation.
  repeat split; now intros F.
Qed.
Next Obligation.
  repeat split; now intros F.
Qed.

#[program, local]
Fixpoint string_of_Z_aux
         (acc: string)
         (n: Z | 0 <= n)
         {measure (Z.to_nat n)} :=
  match n =? 0 as n in bool with
  | true
    => acc
  | false
    => string_of_Z_aux (String (ascii_of_Z (n mod 10)) acc)
                         (n / 10)
  end.

Next Obligation.
  now apply Z.mod_pos_bound.
Qed.

Next Obligation.
  now apply Z.div_pos.
Qed.

Next Obligation.
  apply Z2Nat.inj_lt.
  + now apply Z.div_pos.
  + exact H.
  + apply Z.div_lt; [| repeat constructor].
    symmetry in Heq_n.
    apply Z.eqb_neq in Heq_n.
    lia.
Qed.

#[program]
Definition string_of_Z
           (n:  Z)
  : string :=
  if Z_lt_le_dec n 0
  then append "-" (string_of_Z_aux "" (Z.abs n))
  else if Z.eq_dec n 0
       then "0"
       else string_of_Z_aux "" n.

Next Obligation.
  apply Z.abs_nonneg.
Qed.

Definition Z_of_string (s: string) :=
  let fix aux acc s :=
      match s with
      | String "0" rst => aux (10 * acc) rst
      | String "1" rst => aux (1 + 10 * acc) rst
      | String "2" rst => aux (2 + 10 * acc) rst
      | String "3" rst => aux (3 + 10 * acc) rst
      | String "4" rst => aux (4 + 10 * acc) rst
      | String "5" rst => aux (5 + 10 * acc) rst
      | String "6" rst => aux (6 + 10 * acc) rst
      | String "7" rst => aux (7 + 10 * acc) rst
      | String "8" rst => aux (8 + 10 * acc) rst
      | String "9" rst => aux (9 + 10 * acc) rst
      | _ => acc
      end
  in
  match s with
  | String "-" rst => -1 * aux 0 rst
  | _ => aux 0 s
  end.