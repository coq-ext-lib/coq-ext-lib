Require Import ExtLib.Data.Monads.IStateMonad.
Require Import ExtLib.Structures.IXMonad.

Section example.

  Import IxMonadNotation.
  Local Open Scope ixmonad_scope. 
        
  Variables A B C : Type.

  Variable function1 : A -> B.
  Variable function2 : B -> C.

  Definition update1 : istate A B unit :=
    modify_ function1.

  Definition update2 : istate B C unit :=
    modify_ function2.

  Definition compose : istate A C unit :=
    update1 ;;
    update2.

End example.