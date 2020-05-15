From Coq Require Import Program.Equality FunInd.
From Base Require Import Init Equality Monad.

Inductive list_equal `{EquP a} : list a -> list a -> Prop :=
| nil_equal : list_equal [] []
| cons_equal (x y : a) (rst rst' : list a) (equ1 : x === y)
    (equ2 : list_equal rst rst')
  : list_equal (x :: rst) (y :: rst').

Arguments cons_equal [a _] (x y rst rst' equ1 equ2).
Arguments nil_equal {a _}.

Instance list_EquP `(EquP a) : EquP (list a) :=
  { equal := list_equal }.

Lemma list_equal_refl `{EquP' a} (x : list a) : list_equal x x.

Proof.
  induction x.
  + apply nil_equal.
  + now apply cons_equal.
Qed.

Lemma list_equal_sym `{EquP' a} (x y : list a) (equ : list_equal x y)
  : list_equal y x.

Proof.
  induction equ.
  + apply nil_equal.
  + apply cons_equal.
    ++ now symmetry.
    ++ apply IHequ.
Qed.

Lemma list_equal_trans `{EquP' a} (x y z : list a) (equ : list_equal x y)
    (equ' : list_equal y z)
  : list_equal x z.

Proof.
  revert y z equ equ'.
  induction x.
  + intros y z equ equ'.
    inversion equ; subst.
    apply equ'.
  + intros y z equ equ'.
    inversion equ; subst.
    inversion equ'; subst.
    apply cons_equal.
    ++ transitivity y0; auto.
    ++ eapply IHx; eauto.
Qed.

#[program]
Instance list_EquP' `(EquP' a) : EquP' (list a).

Next Obligation.
  constructor.
  + unfold RelationClasses.Reflexive.
    apply list_equal_refl.
  + unfold RelationClasses.Symmetric.
    apply list_equal_sym.
  + unfold RelationClasses.Transitive.
    apply list_equal_trans.
Qed.

Fixpoint list_equalb `{Equ a} (x y : list a) : bool :=
  match x, y with
  | x :: rst, y :: rst' => (x == y) && list_equalb rst rst'
  | [], [] => true
  | _, _ => false
  end.

Functional Scheme list_equalb_ind := Induction for list_equalb Sort Type.

Instance list_Equ `(Equ a) : Equ (list a) :=
  { equalb := list_equalb }.

#[refine]
Instance list_Equ' `(Equ' a) : Equ' (list a) := {}.

Proof.
  intros x y.
  functional induction (list_equalb x y).
  + split; reflexivity.
  + split;  intros equ; [ inversion equ | discriminate ].
  + split;  intros equ; [ inversion equ | discriminate ].
  + split; intros equ.
    ++ inversion equ; subst.
       cbn in *.
       apply Bool.andb_true_iff.
       rewrite <- IHb.
       rewrite equal_equalb_equiv in equ1; [| apply H2].
       rewrite equ1.
       split; [ reflexivity | apply equ2 ].
    ++ cbn in equ.
       apply Bool.andb_true_iff in equ.
       destruct equ as [ equ1 equ2 ].
       rewrite <- equal_equalb_equiv in equ1; [| apply H2].
       constructor; [ apply equ1 |].
       cbn in *.
       now apply IHb.
Qed.

Fixpoint list_map {a b} (f : a -> b) (l : list a) : list b :=
  match l with
  | x :: rst => f x :: list_map f rst
  | [] => []
  end.

Instance list_Functor : Functor list :=
  { map := @list_map }.

Definition list_pure {a} (x : a) : list a := [x].

Definition list_bind {a b} (x : list a) (f : a -> list b) :=
  concat (f <$> x).

Definition list_apply {a b} (f : list (a -> b)) (x : list a) : list b :=
  list_bind f (fun f => f <$> x).

Instance list_Applicative : Applicative list :=
  { pure := @list_pure
  ; apply := @list_apply
  }.

Instance list_Monad : Monad list :=
  { bind := @list_bind }.

Module ListExtraction.
  Extract Inductive list => list [ "[]" "( :: )" ].

  Extract Constant rev => "List.rev".
End ListExtraction.
