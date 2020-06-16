From Coq Require Import Setoid Morphisms.
From Base Require Export Applicative.

Class Monad (m : Type -> Type) `{Applicative m} : Type :=
  { bind {a b} : m a -> (a -> m b) -> m b }.

Arguments bind [m _ _ _ a b] (_ _).

Notation "f >>= g" :=
  (bind f g)
    (at level 20, left associativity) : base_scope.

Notation "'let*' a ':=' p 'in' q" :=
  (bind p (fun a => q))
    (at level 61, a ident, p constr, right associativity, format
    "'[v' 'let*'  a  ':='  p  'in' '/' q ']'")
  : base_scope.

Notation "p ';;' q" := (p >>= fun _ => q)
  (at level 61, right associativity, format
  "'[v' p ';;' '/' q ']'") : base_scope.

Notation "'begin' x 'end'" := x (only parsing) : base_scope.

Definition join {a} `{Monad m} (x : m (m a)) : m a := x >>= id.
Definition void {a} `{Monad m} (x : m a) : m unit := x *> pure tt.
Definition when {a} `{Monad m} (cond : bool) (x : m a) : m unit :=
  if cond
  then void x
  else pure tt.

Class MonadL (m : Type -> Type) `{ApplicativeL m, ! Monad m} : Type :=
  { bind_left_identity {a b} `{EquPropL b} (x : a) (f : a -> m b)
    : pure x >>= f === f x
  ; bind_right_identity {a} `{EquPropL a} (x : m a)
    : x >>= (fun y => pure y) === x
  ; bind_associativity {a b c} `{EquPropL c} (f : m a) (g : a -> m b) (h : b -> m c)
    : (f >>= g) >>= h === f >>= (fun x => (g x) >>= h)
  ; bind_morphism {a b} `{EquPropL b} (x : m a) (f f' : a -> m b)
    : f === f' -> bind x f === bind x f'
  ; bind_map {a b} `{EquPropL b} (x : m a) (f : a -> b)
    : f <$> x === (x >>= (fun y => pure (f y)))
  }.

#[program]
Instance bind_Proper `(MonadL m, EquPropL b) (a : Type)
  : Proper (@eq (m a) ==> @equal (a -> m b) _ ==> @equal (m b) _) (@bind m _ _ _ _ _).

Next Obligation.
  add_morphism_tactic.
  intros x f g equ.
  apply bind_morphism.
  exact equ.
Qed.
