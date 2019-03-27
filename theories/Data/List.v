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

Require Import Prelude.Data.Option.
Require Import Prelude.Control.

Local Open Scope program_scope.
Local Open Scope prelude_scope.

Local Open Scope prelude_scope.

Inductive fold_left_spec
          {a b:  Type}
          (f:    b -> a -> b)
          (init: b)
  : list a -> b -> Prop :=
| fold_left_nil: fold_left_spec f init nil init
| fold_left_rec (x: a)
                (y: b)
                (Heq: y = f init x)
                (rst: list a)
                (acc: b)
  : fold_left_spec f y rst acc -> fold_left_spec f init (cons x rst) acc.

Inductive fold_right_spec
          {a b:  Type}
          (f:    a -> b -> b)
          (init: b)
  : list a -> b -> Prop :=
| fold_right_nil: fold_right_spec f init nil init
| fold_right_rec (x:         a)
                 (rst: list  a)
                 (acc acc':  b)
                 (Hres:      fold_right_spec f init rst acc)
  : fold_right_spec f init (cons x rst) (f x acc).

#[program]
Fixpoint fold_left
         {a b:  Type}
         (l:    list a)
         (acc:  b)
         (f:    b -> a -> b)
  : { y: b | fold_left_spec f acc l y } :=
  match l with
  | nil => acc
  | cons x rst => fold_left rst (f acc x) f
  end.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  econstructor.
  + reflexivity.
  + exact f0.
Defined.

#[local]
Definition fold_right_aux
           {a b: Type}
           (f: a -> b -> b)
  : (b -> b) -> a -> b -> b :=
  fun (cont: b -> b) => fun x res => cont (f x res).

#[program]
Fixpoint fold_right
        {a b:  Type}
        (l:    list a)
        (acc:  b)
        (f:    a -> b -> b)
  : { y: b | fold_right_spec f acc l y } :=
  fold_left l id (fold_right_aux f) acc.
Next Obligation.
Admitted.

#[program]
Inductive map_filter_specs
          {a b: Type}
          (filter: a -> option b)
  : list a -> list b -> Prop :=
| MapFilterNone: map_filter_specs filter nil nil
| MapFilterSome (l:   list a)
                (l':  list b)
                (x:   a)
                (H:   map_filter_specs filter l l')
  : map_filter_specs filter (cons x l) (maybe id cons (filter x) l').

#[program]
Definition map_filter
           {a b:  Type}
           (l:    list a)
           (f:    a -> option b)
  : { l': list b | map_filter_specs f l l' } :=
  fold_right l nil (maybe id cons <<< f).
Next Obligation.
  destruct fold_right as [acc Hacc]; cbn in *.
  unfold compose in *.
  revert acc Hacc.
  induction l; intros acc Hacc.
  + inversion Hacc; subst.
    constructor.
  + inversion Hacc; subst.
    apply IHl in Hres.
    now constructor.
Qed.

#[program]
Lemma map_filter_Some
      {a:  Type}
      (l:  list a)
  : l = map_filter l Some.
Proof.
  destruct (map_filter l Some) as [l' Hspec].
  cbn.
  induction Hspec.
  + reflexivity.
  + cbn.
    now rewrite IHHspec.
Qed.

#[program]
Lemma map_filter_None
      {a b:  Type}
      (l:  list a)
  : nil = map_filter l (fun _ => @None b).
Proof.
  destruct map_filter as [l' Hspec].
  cbn.
  induction Hspec.
  + reflexivity.
  + now rewrite IHHspec.
Qed.