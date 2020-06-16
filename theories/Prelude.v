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

(** We introduce <<coq-base>>, a base library to program in Coq. <<coq-base>> is
    built upon two main objectives: provide the missing pieces of the standard
    library (e.g., a monad typeclass hierarchy, signed primitive integers), and
    offer a comprehensive extraction experience.

    This module re-exports the most useful components of <<coq-base>>.

    Note: Each typeclass comes with two variants. For instance, the [Functor]
    typeclass comes with a variant named [FunctorL]. [Functor] provides the
    _functions_, while [FunctorL] provides the _laws_. *)

(** * Functional Abstractions *)

(** We provide several well-established typeclass, following the example set by
    Haskell in <<prelude>>. *)

From Base.Control Require Export Functor Applicative Monad.

(** * Data *)

From Base.Data Require Export

(** In addition to the built-in equality of Coq, we provide a typeclass
    hierarchy to more easily work with ad-hoc equalities (ideally, one per
    type). *)

     Equality

(** Besides, we provide typeclass implementations and extraction modules for a
    set of “base” types. *)

     Function Bool Byte Bytestring Option List Sum.
