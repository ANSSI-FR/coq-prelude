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

From Coq Require Import Wf Utils ZArith.
From Prelude Require Import Init Text Control.

#[local]
Open Scope Z_scope.
#[local]
Open Scope program_scope.

#[program]
Definition wchar_of_digit (x : Z) (xs : x < 10) : wchar :=
  if x <? 1 then "0"
  else if x <? 2 then "1"
  else if x <? 3 then "2"
  else if x <? 4 then "3"
  else if x <? 5 then "4"
  else if x <? 6 then "5"
  else if x <? 7 then "6"
  else if x <? 8 then "7"
  else if x <? 9 then "8"
  else (if x <? 10 as b return (b = (x <? 10) -> wchar)
  then fun _ => w#"9"
  else _)
         eq_refl.

Next Obligation.
  symmetry in H.
  rewrite Z.ltb_ge in H.
  now apply Zle_not_lt in H.
Defined.

#[program]
Fixpoint text_of_Z_aux (x : Z) (xs : 0 < x) {measure (Z.to_nat x)} : text :=
  let d := x / 10 in
  let r := x mod 10 in
  TCons (wchar_of_digit r _) ((if 0 <? d as b return (0 <? d = b -> text)
                               then fun _ => text_of_Z_aux d _
                               else fun _ => TNil) eq_refl).

Next Obligation.
  apply Z.mod_bound_pos.
  + auto with zarith.
  + reflexivity.
Defined.

Next Obligation.
  now apply Z.ltb_lt in H.
Defined.

Next Obligation.
  apply Z2Nat.inj_lt.
  + apply Z.div_pos.
    ++ auto with zarith.
    ++ reflexivity.
  + auto with zarith.
  + now apply Z.div_lt.
Defined.

#[program]
Definition text_of_Z (x : Z) : text :=
  (if 0 <? x as b return (0 <? x = b -> text)
   then fun _ => text_of_Z_aux x _
   else fun _ => t#"0") eq_refl.

Next Obligation.
  now apply Z.ltb_lt in H.
Defined.

Definition digit_of_wchar (x : wchar) : option Z :=
  match x with
  | w#"0" => Some 0
  | w#"1" => Some 1
  | w#"2" => Some 2
  | w#"3" => Some 3
  | w#"4" => Some 4
  | w#"5" => Some 5
  | w#"6" => Some 6
  | w#"7" => Some 7
  | w#"8" => Some 8
  | w#"9" => Some 9
  | _ => None
  end.

Fixpoint Z_of_text_aux (x : text) (acc : Z) : option Z :=
  match x with
  | TCons x rst => do let* x := digit_of_wchar x in
                      Z_of_text_aux rst (10 * acc + x)
                   end
  | TNil => pure acc
  end.

Definition Z_of_text (x : text)  : option Z :=
  match x with
  | TCons w#"-" rst => do (fun x => -1 * x) <$> Z_of_text_aux rst 0 end
  | _ => do (fun x => -1 * x) <$> Z_of_text_aux x 0 end
  end.
