From Base Require Export Init Equality.

Class Functor (f : Type -> Type) : Type :=
  { map {a b} : (a -> b) -> f a -> f b
  }.

Arguments map [f _ a b] (_ _).

Notation "f <$> x" := (map f x) (at level 27, left associativity) : base_scope.

Class FunctorL (f : Type -> Type)
   `{Functor f, forall `(EquProp a), EquProp (f a), ! forall `(EquPropL a), EquPropL (f a)} :=
  { functor_identity {a} `{EquPropL a} (x : f a) : map id x === id x
  ; functor_map_identity {a b c} `{EquPropL c}
      (u : b -> c) (v : a -> b) (x : f a)
    : (u <<< v) <$> x === u <$> map v x
  }.

Definition fconst {f a b} `{Functor f} (x : a) (t : f b) : f a :=
  map (fun _ => x) t.

Notation "f <$ g" := (fconst f g) (at level 27, left associativity) : base_scope.
