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

Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.

Require Import Prelude.PropBool.

(** * Weaker Equality

    For a number of type, the Coq equality is too strong. Therefore,
    we introduce the idea of a _weaker equality_ one can use in place
    of the Leibniz equality used in Coq.

 *)

Class Equality
      (A: Type) :=
  { equal (a a': A): Prop
  ; rel:> Equivalence equal
  }.

Arguments equal [A _] (_ _).

Infix "==" :=
  equal
    (at level 70, no associativity)
  : prelude_scope.

Notation "a /= b" :=
  (~ equal a b)
    (at level 70, no associativity)
  : prelude_scope.

Local Open Scope prelude_scope.

Lemma not_equal_sym
      {A:    Type} `{Equality A}
      (x y:  A)
  : ~ equal x y -> ~ equal y x.
Proof.
  intros Hneq Heq.
  symmetry in Heq.
  apply Hneq in Heq.
  exact Heq.
Qed.

(** * Weaker Decidable Equality

    Sometimes, it is not enough to have an equality. Thus, we
    introduce the notion of weaker decidable equality. It comes in two
    “flavors”: one based on sumbool and one based on bool.

 *)

Class DecidableEquality
      (A:  Type) `{Equality A} :=
  { equal_dec (a a':  A)
    : {equal a a'} + {~ equal a a'}
  }.

Arguments equal_dec [A _ _] (_ _).

Infix "=?" :=
  equal_dec
    (at level 70, no associativity)
  : prelude_scope.

Class EqualityBool
      (A:  Type) `{Equality A} :=
  { equalb (a a':  A)
    : bool
  ; equalb_is_bool_prop :> PropBool2 (@equal A _) equalb
  }.

Arguments equalb [A _ _] (_ _).

Infix "?=" :=
  equalb
    (at level 70, no associativity)
  : prelude_scope.

Lemma equalb_equal
      {A:     Type} `{EqualityBool A}
      (a a':  A)
  : a ?= a' = true <-> a == a'.
Proof.
  apply pred_bool_pred_2.
Qed.

Lemma weq_bool_refl
      {A:  Type} `{EqualityBool A}
      (a:  A)
  : a ?= a = true.
Proof.
  apply equalb_equal.
  reflexivity.
Qed.

Lemma equalb_false
      {A:     Type} `{EqualityBool A}
      (a a':  A)
  : a ?= a' = false <-> a /= a'.
Proof.
  split.
  + intros Hweq_bool Hweq.
    apply (equalb_equal a a') in Hweq.
    rewrite Hweq in Hweq_bool.
    discriminate.
  + intros Hnweq.
    case_eq (a ?= a'); intro Heq.
    ++ apply equalb_equal in Heq.
       apply Hnweq in Heq.
       destruct Heq.
    ++ reflexivity.
Qed.

Lemma equalb_sym
      {A:     Type} `{EqualityBool A}
      (a a':  A)
  : (a ?= a') = (a' ?= a).
Proof.
  case_eq (a ?= a'); intros Heq.
  + apply equalb_equal in Heq.
    symmetry in Heq.
    apply equalb_equal in Heq.
    rewrite <- Heq.
    reflexivity.
  + apply equalb_false in Heq.
    apply not_equal_sym in Heq.
    apply equalb_false in Heq.
    rewrite <- Heq.
    reflexivity.
Qed.

Lemma equalb_false_rewrite
      {A:    Type} `{EqualityBool A}
      (x y:  A)
  : x /= y -> x ?= y = false.
Proof.
  apply equalb_false.
Qed.

(** * Instances

    ** Function Instances

 *)

Definition function_equal
           {a b:  Type} `{Equality b}
           (f g:  a -> b)
  : Prop :=
  forall (x: a), f x == g x.

Lemma function_equal_refl
      {a b:  Type} `{Equality b}
      (f: a -> b)
  : function_equal f f.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma function_equal_sym
      {a b:  Type} `{Equality b}
      (f g:  a -> b)
  : function_equal f g
    -> function_equal g f.
Proof.
  unfold function_equal.
  intros H' x.
  rewrite H'.
  reflexivity.
Qed.

Lemma function_equal_trans
      {a b:    Type} `{Equality b}
      (f g h:  a -> b)
  : function_equal f g
    -> function_equal g h
    -> function_equal f h.
Proof.
  unfold function_equal.
  intros F G x.
  rewrite <- (G x).
  exact (F x).
Qed.

Add Parametric Relation
    (a b:  Type) `{Equality b}
  : (a -> b) (function_equal)
    reflexivity  proved by function_equal_refl
    symmetry     proved by function_equal_sym
    transitivity proved by function_equal_trans
      as function_equal_equiv.

Instance function_Equality
         (a b:  Type)
        `{Equality b}
  : Equality (a -> b) :=
  { equal := function_equal
  }.

(** ** Tuple Instances

 *)

Definition tuple_equal
           {a b:   Type} `{Equality a} `{Equality b}
           (o o':  a * b)
  : Prop :=
  fst o == fst o'
  /\ snd o == snd o'.

Lemma tuple_equal_refl
      {a b:  Type} `{Equality a} `{Equality b}
      (o:    a * b)
  : tuple_equal o o.
Proof.
  split; reflexivity.
Qed.

Lemma tuple_equal_sym
      {a b:   Type} `{Equality a} `{Equality b}
      (o o':  a * b)
  : tuple_equal o o'
    -> tuple_equal o' o.
Proof.
  intros [Hf Hs].
  split; [ rewrite Hf; reflexivity
         | rewrite Hs; reflexivity
         ].
Qed.

Lemma tuple_equal_trans
      {a b:       Type} `{Equality a} `{Equality b}
      (o o' o'':  a * b)
  : tuple_equal o o'
    -> tuple_equal o' o''
    -> tuple_equal o o''.
Proof.
  intros [Of Os] [Of' Os'].
  split; [ rewrite Of; exact Of'
         | rewrite Os; exact Os'
         ].
Qed.

Add Parametric Relation
    (a b:  Type) `{Equality a} `{Equality b}
  : (a * b) (tuple_equal)
    reflexivity  proved by tuple_equal_refl
    symmetry     proved by tuple_equal_sym
    transitivity proved by tuple_equal_trans
      as tuple_equal_equiv.

Instance tuple_Equality
         (a b:  Type) `{Equality a} `{Equality b}
  : Equality (a * b) :=
  { equal := tuple_equal
  }.

Add Parametric Morphism
    (a b:  Type) `{Equality a} `{Equality b}
  : fst
    with signature (@equal (a * b) _) ==> (@equal a _)
      as fst_tuple_equal_morphism.
Proof.
  intros o o' [P Q].
  exact P.
Qed.

Add Parametric Morphism
    (a b:  Type) `{Equality a} `{Equality b}
  : snd
    with signature (@equal (a * b) _) ==> (@equal b _)
      as snd_tuple_equal_morphism.
Proof.
  intros o o' [P Q].
  exact Q.
Qed.

Add Parametric Morphism
    (a b:  Type) `{Equality a} `{Equality b}
  : pair
    with signature (@equal a _) ==> (@equal b _) ==> (@equal (a * b) _)
      as pair_tuple_equal_morphism.
Proof.
  intros o o' Heq p p' Heq'.
  constructor; [ exact Heq
               | exact Heq'
               ].
Qed.

Definition tuple_equal_bool
           {a b:  Type} `{EqualityBool a} `{EqualityBool b}
           (x y:  a * b)
  : bool :=
  (fst x ?= fst y) && (snd x ?= snd y).

Instance tuple_PropBool
         (a b:  Type) `{EqualityBool a} `{EqualityBool b}
  : PropBool2 (@tuple_equal a b _ _) (@tuple_equal_bool a b _ _ _ _) :=
  {}.
+ intros x y.
  unfold tuple_equal_bool.
  unfold tuple_equal.
  split.
  ++ intros Hbool.
     apply andb_prop in Hbool.
     destruct Hbool as [Hb Hb'].
     apply pred_bool_pred_2 in Hb.
     apply pred_bool_pred_2 in Hb'.
     split; [ exact Hb | exact Hb' ].
  ++ intros [Hp Hp'].
     apply pred_bool_pred_2 in Hp.
     apply pred_bool_pred_2 in Hp'.
     apply andb_true_intro.
     split; [ exact Hp | exact Hp' ].
Defined.

(** ** Nat

 *)

Instance nat_Equality
  : Equality nat :=
  { equal := eq
  }.

Instance nat_eq_eqb_PropBool2
  : PropBool2 (@eq nat) (Nat.eqb) :=
  {}.
+ apply Nat.eqb_eq.
Defined.

Instance nat_EqualityBool
  : EqualityBool nat :=
  { equalb := Nat.eqb
  }.

(** ** Z

 *)

Require Import Coq.ZArith.ZArith.

Instance Z_Equality
  : Equality Z :=
  { equal := eq
  }.

(** ** Bool

 *)

Instance bool_Equality
  : Equality bool :=
  { equal := eq
  }.

Instance bool_eq_eqb_PropBool2
  : PropBool2 (@eq bool) (Bool.eqb) :=
  {}.
+ apply Bool.eqb_true_iff.
Defined.

Instance bool_EqualityBool
  : EqualityBool bool :=
  { equalb := Bool.eqb
  }.

(** ** Option

 *)

Inductive option_equal
          {a:    Type}
         `{Equality a}
  : option a -> option a -> Prop :=
| option_equal_some (x:    a)
                    (y:    a)
                    (Heq:  x == y)
  : option_equal (Some x) (Some y)
| option_equal_none
  : option_equal None None.

Lemma option_equal_refl
      {a:  Type} `{Equality a}
      (x:  option a)
  : option_equal x x.
Proof.
  destruct x; constructor.
  reflexivity.
Qed.

Lemma option_equal_sym
      {a:    Type} `{Equality a}
      (x y:  option a)
  : option_equal x y
    -> option_equal y x.
Proof.
  intro Heq.
  destruct x; inversion Heq; constructor.
  symmetry; exact Heq0.
Qed.

Lemma option_equal_trans
      {a:      Type} `{Equality a}
      (x y z:  option a)
  : option_equal x y
    -> option_equal y z
    -> option_equal x z.
Proof.
  intros Heq Heq'.
  induction Heq'.
  + induction x.
    ++ constructor.
       inversion Heq.
       rewrite <- Heq0.
       exact Heq1.
    ++ inversion Heq.
  + inversion Heq.
    constructor.
Qed.

Add Parametric Relation
    (a:  Type) `{Equality a}
  : (option a) (option_equal)
    reflexivity proved by   option_equal_refl
    symmetry proved by      option_equal_sym
    transitivity proved by  option_equal_trans
      as option_equal_relation.

Instance option_Equality
         (a:  Type) `{Equality a}
  : Equality (option a) :=
  { equal := option_equal
  }.

Add Parametric Morphism
    (a:  Type) `{Equality a}
  : (@Some a)
    with signature (@equal a _) ==> (@equal (option a) _)
      as some_equal_morphism.
  + intros x y Heq.
    constructor.
    exact Heq.
Qed.

Definition option_equal_bool
           {a:    Type} `{EqualityBool a}
           (x y:  option a)
  : bool :=
  match x, y with
  | Some x, Some y
    => x ?= y
  | None, None
    => true
  | _, _
    => false
  end.

Instance option_equal_bool_prop
         (a:  Type) `{EqualityBool a}
  : PropBool2 (@equal (option a) _) (@option_equal_bool a _ _) :=
  {}.
+ intros x y.
  split; [ intro Hb | intro Hp ].
  ++ destruct x; induction y; try discriminate.
     +++ constructor.
         apply pred_bool_pred_2.
         exact Hb.
     +++ constructor.
  ++ induction Hp.
     +++ cbn.
         apply pred_bool_pred_2.
         exact Heq.
     +++ reflexivity.
Defined.

Instance option_EqualityBool
         (a:  Type) `{EqualityBool a}
  : EqualityBool (option a) :=
  { equalb := option_equal_bool
  }.

(** ** List

 *)

Inductive list_equal
          {a:  Type} `{Equality a}
  : list a -> list a -> Prop :=
| list_equal_cons (x y:   a)
                  (r r':  list a)
                  (Heq:   x == y)
                  (Heq':  list_equal r r')
  : list_equal (cons x r) (cons y r')
| list_equal_nil
  : list_equal nil nil.

Lemma list_equal_refl
      {a:  Type} `{Equality a}
      (l:  list a)
  : list_equal l l.
Proof.
  induction l.
  + constructor.
  + constructor; [ reflexivity
                 | exact IHl
                 ].
Qed.

Lemma list_equal_sym
      {a:     Type} `{Equality a}
      (l l':  list a)
  : list_equal l l'
    -> list_equal l' l.
Proof.
  intros Heq; induction Heq.
  + constructor.
    ++ symmetry; exact Heq.
    ++ exact IHHeq.
  + constructor.
Qed.

Lemma list_equal_trans
      {a:     Type} `{Equality a}
      (l l' l'':  list a)
  : list_equal l l'
    -> list_equal l' l''
    -> list_equal l l''.
Proof.
  revert l' l''.
  induction l; intros l' l''.
  + intros Heq Heq'.
    inversion Heq; subst.
    inversion Heq'; subst.
    constructor.
  + intros Heq Heq'.
    inversion Heq; subst.
    inversion Heq'; subst.
    constructor.
    ++ rewrite Heq0.
       exact Heq1.
    ++ apply (IHl r' r'0 Heq'0 Heq'1).
Qed.

Add Parametric Relation
    (a:  Type) `{Equality a}
  : (list a) (list_equal)
    reflexivity  proved by list_equal_refl
    symmetry     proved by list_equal_sym
    transitivity proved by list_equal_trans
      as list_equal_equiv.

Instance list_Equality
         (a:  Type) `{Equality a}
  : Equality (list a) :=
  { equal := list_equal
  }.

Fixpoint list_equal_bool
         {a:     Type} `{EqualityBool a}
         (l l':  list a)
  : bool :=
  match l, l' with
  | cons x r, cons x' r'
    => (x ?= x') && (list_equal_bool r r')
  | nil, nil
    => true
  | _, _
    => false
  end.

Instance list_equal_PropBool
         (a:  Type) `{EqualityBool a}
  : PropBool2 (@equal (list a) _) list_equal_bool :=
  {}.
+ induction a0; induction b.
  ++ split; reflexivity.
  ++ split; [ discriminate |].
     intros Hf; inversion Hf.
  ++ split; [ discriminate |].
     intros Hf; inversion Hf.
  ++ split.
     +++ intros Hweq.
         apply Bool.andb_true_iff in Hweq.
         fold list_equal_bool in Hweq.
         destruct Hweq as [H1 H2].
         constructor.
         ++++ apply pred_bool_pred_2.
              exact H1.
         ++++ apply IHa0 in H2.
              exact H2.
     +++ intros Heq.
         inversion Heq; subst.
         apply Bool.andb_true_iff.
         fold list_equal_bool.
         apply pred_bool_pred_2 in Heq0.
         split; [ exact Heq0 |].
         apply IHa0.
         exact Heq'.
Qed.

Instance list_EqualityBool
         (a:  Type) `{EqualityBool a}
  : EqualityBool (list a) :=
  {}.

(** ** String

 *)

Instance string_Equality
  : Equality string :=
  { equal := eq
  }.

Instance string_EqualityDec
  : DecidableEquality string :=
  { equal_dec := string_dec
  }.

Instance string_EqualityBool
  : EqualityBool string :=
  { equalb := fun s s'
              => if string_dec s s'
                 then true
                 else false
  }.
Proof.
  constructor.
  intros s s'.
  split;
    destruct (string_dec s s');
    trivial.
  ++ intros Hf.
     discriminate.
  ++ intros Hf.
     apply n in Hf.
     destruct Hf.
Qed.

(** ** Sigma-type
 *)

Section SigEq.
  Variables (T: Type)
            (P: T -> Prop).

  Inductive sig_eq
           `{Equality T}
            (x y:  { a: T | P a })
    : Prop :=
  | sig_eq_proj1 : proj1_sig x == proj1_sig y -> sig_eq x y.

  Lemma sig_eq_refl
       `{Equality T}
        (x:  { a: T | P a })
    : sig_eq x x.
  Proof.
    now constructor.
  Qed.

  Lemma sig_eq_sym
       `{Equality T}
        (x y:  { a: T | P a })
    : sig_eq x y -> sig_eq y x.
  Proof.
    intros [H1].
    now constructor.
  Qed.

  Lemma sig_eq_trans
       `{Equality T}
        (x y z:  { a: T | P a })
    : sig_eq x y -> sig_eq y z -> sig_eq x z.
  Proof.
    intros [H1] [H2].
    constructor.
    now transitivity (proj1_sig y).
  Qed.
End SigEq.

Arguments sig_eq [T P H] (x y).

Add Parametric Relation
    (T: Type) `{H: Equality T}
    (P: T -> Prop)
  : { a: T | P a } (@sig_eq T P _)
    reflexivity proved by (@sig_eq_refl T P H)
    symmetry proved by (@sig_eq_sym T P H)
    transitivity proved by (@sig_eq_trans T P H)
      as sig_eq_rel.

Instance sigma_Equality
         (T: Type) `{H: Equality T}
         (P: T -> Prop)
  : Equality { a: T | P a } :=
  { equal := @sig_eq T P H
  }.

(** * Tactics

 *)

Ltac rewrite_equal H :=
  lazymatch type of H with
  | (?x ?= ?y) = true
    => match goal with
       | [ |- context[x] ]
         => assert (Heq:  x == y) by (apply equalb_equal; exact H);
            rewrite Heq;
            clear Heq
       | [ |- context[y] ]
         => assert (Heq:  x == y) by (apply equalb_equal; exact H);
            rewrite <- Heq;
            clear Heq
       end || fail "nothing to rewrite"
  | ?x == ?y
    => match goal with
       | [ |- context[x] ]
         => rewrite H
       | [ |- context[y] ]
         => rewrite <- H
       end || fail "nothing to rewrite"
  | _ => fail "argument should be of the form x == y or x ?= y"
  end.

Ltac rewrite_equal_bool H :=
  lazymatch type of H with
  | (?x ?= ?y) = _
    => match goal with
       | [ |- context [x ?= y] ]
         => rewrite H
       | [ |- context [y ?= x] ]
         => rewrite (equalb_sym y x);
            rewrite H
       end || fail "nothing to rewrite"
  | ?x == ?y
    => match goal with
       | [ |- context[x ?= y] ]
         => rewrite H; rewrite weq_bool_refl
       | [ |- context[y ?= x] ]
         => rewrite (equalb_sym y x);
            rewrite H;
            rewrite weq_bool_refl
       end || fail "nothing to rewrite"
  | ?x /= ?y
    => match goal with
       | [ |- context[x ?= y] ]
         => fail "todo"
       | [ |- context[y ?= x] ]
         => fail "todo"
       end || fail "nothing to rewrite"
  | _ => fail "argument should be of the form x == y or x ?= y"
  end.