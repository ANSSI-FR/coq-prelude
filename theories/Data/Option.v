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

Require Import Coq.Program.Utils.

Require Import Prelude.Control.
Require Import Prelude.Data.Either.

Local Open Scope program_scope.
Local Open Scope prelude_scope.

Program Definition is_some
        {a:  Type}
        (o:  option a)
  : { exists x, o = Some x } + { o = None } :=
  match o with
  | Some x => left $ ex_intro (eq (Some x) <<< Some) x eq_refl
  | None => right eq_refl
  end.

Program Definition is_none
        {a:  Type}
        (o:  option a)
  : { o = None } + { exists x, o = Some x } :=
  match o with
  | None => left eq_refl
  | Some x =>  right $ ex_intro (eq (Some x) <<< Some) x eq_refl
  end.

#[program]
Definition from_some
           {a:  Type}
           (o:  option a | exists x, o = Some x)
  : { y: a | `o = Some y } :=
  match o with
  | Some x => x
  | None => !
  end.

#[program]
Definition maybe
           {a b:  Type}
           (x:    b)
           (f:    a -> b)
           (o:    option a)
  : { y: b | if is_some o then y = f (from_some o) else y = x } :=
  match o with
  | None   => x
  | Some z => f z
  end.
Next Obligation.
  now exists H.
Qed.

#[program]
Definition from_option
           {a:  Type}
           (x:  a)
           (o:  option a)
  : { y: a | maybe (y = x) (eq y) o }:=
  maybe x id o.
Next Obligation.
  now induction o.
Qed.

Lemma sat_is_some_unsat_is_none
      {a:  Type}
      (o:  option a)
  : sat (is_some o) -> unsat (is_none o).
Proof.
  now induction o.
Qed.