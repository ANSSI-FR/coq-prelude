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

From Prelude Require Import Init Control.

Class Alternative (f : Type -> Type) `{Applicative f} :=
  { empty {α} : f α
  ; alt {α} (p q : f α) : f α
  ; many {α} (p : f α) : f (list α)
  }.

Arguments empty {f _ _ α}.
Arguments alt [f _ _ α] p%monad q%monad.
Arguments many [f _ _ α] p%monad.

Infix "<|>" := alt (at level 50, left associativity) : monad_scope.

Definition some `{Alternative f} {α} : f α -> f (list α) :=
  fun* p => cons <$> p <*> many p.

Arguments some [f _ _ α] p%monad.

Definition optional `{Alternative f} {α} : f α -> f (option α) :=
  fun* (p : f α) => (Some <$> p) <|> empty.

Arguments optional [f _ _ α] p%monad.
