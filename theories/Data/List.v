Require EquivDec.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

Section type.
  Variable T : Type.
  Context {type_T : type T}.

  Inductive list_eq : list T -> list T -> Prop :=
  | nil_eq : list_eq nil nil
  | cons_eq : forall x xs y ys, equal x y -> list_eq xs ys -> list_eq (x :: xs) (y :: ys).

  Instance type_list : type (list T) :=
  { equal := list_eq
  ; proper := Forall proper
  }.

  Context {typeOk_T : typeOk type_T}.
  
  Instance typeOk_list : typeOk type_list.
  Proof.
    constructor.
    { intros. induction H.
      { intuition; constructor. }
      { apply only_proper in H; auto. intuition; constructor; intuition. } }
    { intro. induction x; intros.
      { constructor. }
      { inversion H; clear H; subst. 
        constructor; auto. 
        apply equiv_prefl; auto. apply IHx. apply H3. } }
    { intro. induction 1; constructor; auto.
      apply equiv_sym; auto. }
    { intro. do 3 intro.  revert z. induction H. 
      { remember nil. destruct 1; try congruence. constructor. }
      { remember (y :: ys). destruct 1; try congruence. inversion Heql; clear Heql; subst.
        constructor. eapply equiv_trans; eauto. eapply IHlist_eq. apply H2. } }
  Qed.
End type.

Section EqDec.
  Variable T : Type.
  Variable EqDec_T : EquivDec.EqDec _ (@eq T).

  Global Instance EqDec_list : EquivDec.EqDec _ (@eq (list T)).
  Proof.
    red. unfold Equivalence.equiv, RelationClasses.complement.
    intros.
    change (x = y -> False) with (x <> y).
    decide equality. eapply EqDec_T.
  Qed.
End EqDec.

Section AllB.
  Variable T : Type.
  Variable p : T -> bool.

  Fixpoint allb (ls : list T) : bool :=
    match ls with
      | nil => true
      | l :: ls =>
        if p l then allb ls else false
    end.

  Fixpoint anyb (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls =>
        if p l then true else anyb ls
    end.
End AllB.

Global Instance Foldable_list {T} : Foldable (list T) T :=
  fun _ f x ls => fold_right f x ls.

Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Applicative.

Global Instance Traversable_list : Traversable list :=
{ mapT := fun F _ A B f =>
  List.fold_right (fun x acc => ap (ap (pure (@cons B)) (f x)) acc) (pure nil)
}.

Global Instance Monad_list : Monad list :=
{ ret  := fun _ x => x :: nil
; bind := fun _ _ x f =>
  List.fold_right (fun x acc => f x ++ acc) nil x
}.

Section list.
  Inductive R_list_len {T} : list T -> list T -> Prop :=
  | R_l_len : forall n m, length n < length m -> R_list_len n m.

  Theorem wf_R_list_len T : well_founded (@R_list_len T).
  Proof.
    constructor. intros.
    refine (@Fix _ _ wf_R_lt (fun n : nat => forall ls : list T, n = length ls -> Acc R_list_len ls)
      (fun x rec ls pfls => Acc_intro _ _)
      _ _ refl_equal).
    refine (
      match ls as ls return x = length ls -> forall z : list T, R_list_len z ls -> Acc R_list_len z with
        | nil => fun (pfls : x = 0) z pf => _
        | cons l ls => fun pfls z pf =>
          rec _ (match pf in R_list_len xs ys return x = length ys -> R_nat_lt (length xs) x with
                   | R_l_len n m pf' => fun pf_eq => match eq_sym pf_eq in _ = x return R_nat_lt (length n) x with
                                                     | refl_equal => R_lt pf'
                                                   end
                 end pfls) _ eq_refl
      end pfls).
    clear - pf; abstract (inversion pf; subst; simpl in *; inversion H).
  Defined.
End list.
