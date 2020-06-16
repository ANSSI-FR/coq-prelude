From Coq Require Import Program.Equality Equivalence.
From Base Require Export Init Equality Monad.

Inductive option_equal `{EquProp a} : option a -> option a -> Prop :=
| option_equal_Some (x y : a) (equ : x === y) : option_equal (Some x) (Some y)
| option_equal_None : option_equal None None.

Lemma option_equal_refl `{EquPropL a} (x : option a) : option_equal x x.

Proof.
  destruct x; constructor.
  reflexivity.
Qed.

Lemma option_equal_sym `{EquPropL a} (x y : option a) (equ : option_equal x y)
  : option_equal y x.

Proof.
  induction equ; subst; constructor.
  now symmetry.
Qed.

Lemma option_equal_trans `{EquPropL a} (x y z : option a)
    (equ1 : option_equal x y) (equ2 : option_equal y z)
  : option_equal x z.

Proof.
  induction equ1;
    dependent induction equ2;
    constructor.
  now transitivity y.
Qed.

#[program]
Instance option_Equivalence `(EquPropL a) : Equivalence option_equal.

Next Obligation.
  unfold Reflexive.
  apply option_equal_refl.
Qed.

Next Obligation.
  unfold Symmetric.
  apply option_equal_sym.
Qed.

Next Obligation.
  unfold Transitive.
  apply option_equal_trans.
Qed.

Instance option_EquProp `(EquProp a) : EquProp (option a) :=
  { equal := option_equal }.

#[program]
Instance option_EquPropL `(EquPropL a) : EquPropL (option a).

Definition option_equalb `{Equ a} (x y : option a) : bool :=
  match x, y with
  | Some x, Some y => x == y
  | None, None => true
  | _, _ => false
  end.

Instance option_Equ `(Equ a) : Equ (option a) :=
  { equalb := option_equalb }.

#[refine]
Instance option_EquL `(EquL a)
  : EquL (option a) := {}.

Proof.
  intros x y.
  split.
  + intros equ.
    induction equ.
    ++ cbn.
       rewrite <- equal_equalb_equiv; [ exact equ | exact H2 ].
    ++ reflexivity.
  + intros equ.
    destruct x; destruct y; cbn in equ; try discriminate.
    ++ constructor.
       rewrite equal_equalb_equiv; [ exact equ | exact H2 ].
    ++ reflexivity.
Qed.

Instance option_Functor : Functor option :=
  { map := option_map }.

#[refine]
Instance option_FunctorL : FunctorL option := {}.

Proof.
  + now intros a H H' [ x |].
  + now intros a b c H H' u v [ x |].
Defined.

Definition option_pure {a} (x : a) : option a := Some x.

Instance option_pure_EquMorphism `(EquProp a) : EquMorphism (@option_pure a).

Proof.
  add_morphism_tactic.
  intros x y equ.
  now constructor.
Qed.

Definition option_apply {a b} (f : option (a -> b)) (x : option a) : option  b :=
  match f, x with
  | Some f, Some x => Some (f x)
  | _, _ => None
  end.

Instance option_apply_Some_EquMorphism {a b} (f : a -> b)
    `(EquProp a, EquProp b, EquMorphism f)
  : EquMorphism (option_apply (Some f)).

Proof.
  add_morphism_tactic.
  intros [ x |] [ y |] equ; inversion equ; subst; constructor.
  apply H1.
  apply equ0.
Qed.

Instance option_apply_None_EquMorphism `(EquProp a, EquProp b)
  : EquMorphism (@option_apply a b None).

Proof.
  add_morphism_tactic.
  intros [ x |] [ y |] equ; inversion equ; subst; constructor.
Qed.

Instance option_Applicative : Applicative option :=
  { pure := @option_pure
  ; apply := @option_apply
  }.

#[refine]
Instance option_ApplicativeL : ApplicativeL option := {}.

Proof.
  + now intros a H1 H2 [ v |].
  + now intros a b c H1 H2 [ u |] [ v |] [ w |].
  + now intros.
  + now intros a b H1 H2 [ u |] y.
  + now intros a b H1 H2 g [ x |].
Qed.

Definition option_bind {a b} (x : option a) (f : a -> option b) : option b :=
  match x with
  | Some x => f x
  | _ => None
  end.

Instance option_Monad : Monad option :=
  { bind := @option_bind }.


#[refine]
Instance option_MonadL : MonadL option := {}.

Proof.
  + now intros.
  + now intros a Ha Ha' [ x |].
  + now intros a b c Hc Hc' [ f |] g h.
  + intros a b Hb Hb' [ x |] f f'; intros equ.
    ++ apply equ.
    ++ reflexivity.
  + now intros a b Hb Hb' [ x |] f.
Qed.

Module OptionExtraction.
  Extract Inductive option => option [ Some None ].
End OptionExtraction.
