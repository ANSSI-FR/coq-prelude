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

Require Import Prelude.Equality.
Require Import Prelude.Control.

Local Open Scope prelude_scope.

Axioms (IO:           Type -> Type)
       (io_map:       forall {a b:  Type},
           (a -> b) -> IO a -> IO b)
       (io_pure:      forall {a:  Type},
           a -> IO a)
       (io_apply:     forall {a b:  Type},
           IO (a -> b) -> IO a -> IO b)
       (io_bind:      forall {a b:  Type},
           IO a -> (a -> IO b) -> IO b).

Instance Equality_IO
         (A:  Type)
        `{Equality A}
  : Equality (IO A).
Admitted.

Conjectures (io_map_id:  forall (a:  Type)
                                (H:  Equality a)
                                (x:  IO a),
                io_map id x == id x)
            (io_map_compose:  forall (a b c:  Type)
                                     (H:      Equality c)
                                     (u:      b -> c)
                                     (v:      a -> b)
                                     (x:      IO a),
                io_map (v >>> u) x == (io_map v >>> io_map u) x)
              (io_apply_id: forall (a:  Type)
                                   (H:  Equality a)
                                   (v:  IO a),
                  io_apply (io_pure id) v == v)
              (io_apply_compose: forall (a b c:  Type)
                                        (H:      Equality c)
                                        (u:      IO (b -> c))
                                        (v:      IO (a -> b))
                                        (w:      IO a),
                  io_apply (io_apply (io_apply (io_pure compose) u) v) w
                  == io_apply u (io_apply v w))
              (io_apply_homo: forall (a b:  Type)
                                     (H:    Equality b)
                                     (v:    a -> b)
                                     (x:    a),
                  io_apply (io_pure v) (io_pure x) == io_pure (v x))
              (io_apply_interchange: forall (a b:  Type)
                                            (H:    Equality b)
                                            (u:    IO (a -> b))
                                            (y:    a),
                  io_apply u (io_pure y)
                  ==  io_apply (io_pure (fun z : a -> b => z y)) u)
              (io_apply_pure_map: forall (a b:  Type)
                                         (H:    Equality b)
                                         (g:    a -> b)
                                         (x:    IO a),
                  io_map g x == io_apply (io_pure g) x)
              (io_bind_left_id: forall (a b:  Type)
                                       (H:    Equality b)
                                       (x:    a)
                                       (f:    a -> IO b),
                  io_bind (io_pure x) f == f x)
              (io_bind_right_id: forall (a:  Type)
                                        (H:  Equality a)
                                        (x:  IO a),
                  io_bind x (fun y : a => io_pure y) == x)
              (io_bind_assoc: forall (a b c:  Type)
                                     (H:      Equality c)
                                     (f:      IO a)
                                     (g:      a -> IO b)
                                     (h:      b -> IO c),
                  io_bind (io_bind f g) h
                  == io_bind f (fun x : a => io_bind (g x) h))
              (io_bind_morph: forall (a b:   Type)
                                     (H:     Equality b)
                                     (x:     IO a)
                                     (f f':  a -> IO b),
                  f == f' -> io_bind x f == io_bind x f')
              (io_bind_map: forall (a b:  Type)
                                   (H:    Equality b)
                                   (x:    IO a)
                                   (f:    a -> b),
                  io_map f x == io_bind x (fun y : a => io_pure (f y))).

Instance IO_Functor
  : Functor IO :=
  { map := @io_map
  }.
+ apply io_map_id.
+ apply io_map_compose.
Defined.

Instance IO_Applicative
  : Applicative IO :=
  { pure := @io_pure
  ; apply := @io_apply
  }.
+ apply io_apply_id.
+ apply io_apply_compose.
+ apply io_apply_homo.
+ apply io_apply_interchange.
+ apply io_apply_pure_map.
Defined.

Instance IO_Monad
  : Monad IO :=
  { bind := @io_bind
  }.
+ apply io_bind_left_id.
+ apply io_bind_right_id.
+ apply io_bind_assoc.
+ apply io_bind_morph.
+ apply io_bind_map.
Defined.