(* coq-base -- A base library to program in Coq
 * Copyright (C) 2018–2020 ANSSI
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

From Base Require Import Equality.

(** * Ad-hoc Equality *)

Instance bool_Equ : Equ bool :=
  { equalb := Bool.eqb }.

#[program]
Instance bool_EquL : EquL bool.

Next Obligation.
  now rewrite Bool.eqb_true_iff.
Qed.

(** * Extraction *)

Module BoolExtraction.
  Extract Inductive bool => bool ["true" "false"].
  Extract Inlined Constant andb => "(&&)".
  Extract Inlined Constant orb => "(||)".
  Extract Constant negb => "Bool.not".
End BoolExtraction.
