Require Import ExtLib.Structures.Monad.
Import Applicative. 

Set Implicit Arguments.
Set Strict Implicit.

Polymorphic Class IxMonad@{d c} (m : Type@{d} -> Type@{d} -> Type@{c} -> Type@{c}) : Type :=
{ ret : forall {i : Type@{d}} {a : Type@{d}}, a -> m i i a
; bind : forall {i j k a b: Type@{d}}, m i j a -> (a -> m j k b) -> m i k b
}.

Module IxMonadNotation.

  Delimit Scope ixmonad_scope with ixmonad.

  Notation "c >>= f" := (@bind _ _ _ _ _ _ _ c f) (at level 50, left associativity) : ixmonad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ _ _ _ c f) (at level 51, right associativity) : ixmonad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : ixmonad_scope.

  Notation "e1 ;; e2" := (_ <- e1%ixmonad ;; e2%ixmonad)%ixmonad
    (at level 100, right associativity) : ixmonad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ _ _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

End IxMonadNotation.

  Polymorphic Instance Applicative_Monad {m i} {M:IxMonad m}
    : Applicative (m i i) :=
    {| Applicative.pure := fun (A : Type) (X : A) => ret X
       ; Applicative.ap := fun (A B : Type) (X : m i i (A -> B)) (X0 : m i i A) => bind X (fun X1 : A -> B => bind X0 (fun X2 : A => ret (X1 X2)))
    |}.
  
  