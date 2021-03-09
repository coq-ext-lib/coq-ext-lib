Require Import ExtLib.Structures.IXMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section IStateType.

  Record istate (i s t: Type) : Type := mkIState
  { runIState : i -> t * s }.

  Definition evalState {i s t} (c : istate i s t) (s : i) : t :=
    fst (runIState c s).

  Definition execState {i s t} (c : istate i s t) (st : i) : s :=
    snd (runIState c st).


  Global Instance IMonad_Ixstate : IxMonad istate  :=
    {
      ret  := fun _ _ v => mkIState (fun s => (v, s))
      ; bind := fun _ _ _ _ _ c1 c2 =>
                   mkIState (fun s =>
                               let (v,s) := runIState c1 s in
                               runIState (c2 v) s)
    }.
  
Definition get {i : Type} := @mkIState i i i (fun s => (s,s)).
Definition put {i o : Type} := (fun v => @mkIState i o unit (fun _ => (tt, v))).
Definition put_  {i o : Type} (s : o) : istate i o unit := (bind (put s) (fun _ => ret tt)). 
Definition modify {i o : Type} (f : i -> o) : istate i o i :=
  bind get (fun x : i => bind (put (f x)) (fun _ : unit => ret x)).
Definition modify_ {i o : Type} (f : i -> o) : istate i o unit :=
  bind (modify f) (fun _ => ret tt).

End IStateType.
