(* FreeSpec
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

Require Import Coq.Setoids.Setoid.
From Equations Require Import Equations Signature.

Require Import Prelude.Control.
Require Import Prelude.Equality.

Local Open Scope prelude_scope.
Local Open Scope list_scope.

Add Parametric Morphism
    (a:  Type)
   `{Equality a}
  : cons
    with signature (@equal a _)
                     ==> (@equal (list a) _)
                     ==> (@equal (list a) _)
      as cons_morphism.
Proof.
  intros x y Heqx r q Eqrst.
  constructor.
  exact Heqx.
  cbn in Eqrst.
  exact Eqrst.
Qed.

(* WORK IN PROGRESS *)

Equations list_map {a b:  Type} (f:  a -> b) (l:  list a) : list b :=
list_map _ nil := nil;
list_map f (cons x r) := (f x) :: (list_map f r).

Add Parametric Morphism
    (a b:  Type)
   `{Equality a}
   `{Equality b}
  : list_map
    with signature (@equal (a -> b) _)
                     ==> eq
                     ==> (@equal (list b) _)
      as list_map_morphism.
Proof.
  intros f g Heq s.
  cbn.
  induction s.
  + repeat rewrite list_map_equation_1.
    reflexivity.
  + repeat rewrite list_map_equation_2.
    constructor.
    ++ apply Heq.
    ++ exact IHs.
Qed.

Lemma list_map_nil
      {a b:  Type}
      (f:    a -> b)
  : list_map f nil = nil.
Proof.
 reflexivity.
Qed.

Instance list_Functor
  : Functor list :=
  { map := @list_map
  }.
+ intros a Ha x.
  induction x.
  ++ reflexivity.
  ++ rewrite list_map_equation_2.
     rewrite IHx.
     reflexivity.
+ induction x.
  ++ reflexivity.
  ++ rewrite list_map_equation_2.
     rewrite IHx.
     reflexivity.
Defined.

Definition list_pure
           {a:  Type}
           (x:  a)
  : list a :=
  x :: nil.

Equations concat {a:  Type} (l l':  list a) : list a :=
concat nil l' := l';
concat (cons x r) l' := x :: concat r l'.

Add Parametric Morphism
    (a:  Type)
   `{Equality a}
  : concat
    with signature (@equal (list a) _)
                     ==> (@equal (list a) _)
                     ==> (@equal (list a) _)
      as concat_list_morphism.
Proof.
  induction x.
  + intros y Heq r s Heqr.
    inversion Heq; subst.
    exact Heqr.
  + intros y Heq r s Heqr.
    inversion Heq; subst.
    Search concat.
    repeat rewrite concat_equation_2.
    constructor.
    ++ exact Heq0.
    ++ apply IHx.
       exact Heq'.
       exact Heqr.
Qed.

Lemma concat_nil
      {a:  Type}
      (l:  list a)
  : concat l nil = l.
Proof.
  induction l.
  + reflexivity.
  + rewrite concat_equation_2.
    rewrite IHl.
    reflexivity.
Qed.

Equations list_app {a b:  Type} (f:  list (a -> b)) (l:  list a) : list b :=
list_app (cons f r) l := concat (f <$> l) (list_app r l);
list_app nil _ := nil.

Equations list_app' {a b:  Type} (x:  a) (f:  list (a -> b)) (l:  list a) : list b :=
list_app' x (cons f r) l := concat (list_pure (f x)) (concat (f <$> l) (list_app' x r l));
list_app' _ nil _ := nil.

Lemma list_app_list_app'
      {a b:  Type}
      (lf:   list (a -> b))
      (x:    a)
      (rst:  list a)
  : list_app lf (x :: rst) = list_app' x lf rst.
Proof.
  induction lf.
  + rewrite list_app_equation_1.
    rewrite list_app'_equation_1.
    reflexivity.
  + rewrite list_app_equation_2.
    rewrite list_app'_equation_2.
    rewrite concat_equation_2.
    rewrite concat_equation_1.
    rewrite IHlf.
    cbn.
    rewrite list_map_equation_2.
    rewrite concat_equation_2.
    reflexivity.
Qed.

Lemma list_app_nil
      {a b:  Type}
      (f:    list (a -> b))
  : list_app f nil = nil.
Proof.
  induction f.
  + reflexivity.
  + rewrite list_app_equation_2.
    rewrite concat_equation_1.
    exact IHf.
Qed.

Add Parametric Morphism
    (a b:  Type)
   `{Equality a}
   `{Equality b}
  : list_app
    with signature (@equal (list (a -> b)) _)
                     ==> eq
                     ==> (@equal (list b) _)
      as list_app_morphism.
Proof.
  intros x y Heq.
  induction Heq.
  + intros s.
    repeat rewrite list_app_equation_2.
    rewrite Heq.
    rewrite IHHeq.
    reflexivity.
  + intros s.
    rewrite list_app_equation_1.
    reflexivity.
Qed.

Conjecture list_conjecture_applicative_1
  : forall (a b c:  Type) `{Equality c}
           (u:      list (b -> c))
           (v:      list (a -> b))
           (w:      list a),
    list_app (list_app (list_app (list_pure compose) u) v) w
    == list_app u (list_app v w).

Instance list_Applicative
  : Applicative (list) :=
  { pure   := @list_pure
  ; apply  := @list_app
  }.
Proof.
  + intros a Heq v.
    induction v.
    ++ reflexivity.
    ++ cbn in *.
       rewrite list_app_equation_2.
       rewrite list_app_equation_1.
       rewrite concat_nil.
       rewrite functor_identity.
       reflexivity.
  + apply list_conjecture_applicative_1.
  + intros a b Heq v x.
    rewrite list_app_equation_2.
    rewrite list_app_equation_1.
    rewrite concat_nil.
    cbn.
    rewrite list_map_equation_2.
    rewrite list_map_equation_1.
    reflexivity.
  + intros a b H u y.
    induction u.
    ++ rewrite list_app_equation_1.
       rewrite list_app_nil.
       reflexivity.
    ++ rewrite list_app_equation_2.
       rewrite IHu.
       cbn.
       rewrite list_map_equation_2.
       rewrite concat_equation_2.
       rewrite concat_equation_1.
       rewrite list_app_equation_2.
       rewrite list_app_equation_1.
       rewrite concat_nil.
       rewrite list_app_equation_2.
       rewrite list_app_equation_1.
       rewrite concat_nil.
       cbn.
       rewrite list_map_equation_2.
       reflexivity.
  + intros a b H g x.
    rewrite list_app_equation_2.
    rewrite list_app_equation_1.
    rewrite concat_nil.
    reflexivity.
Defined.