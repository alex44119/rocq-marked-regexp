(** * Utilities for proofs and tactics
    This file contains helper tactics and common utilities used across
    the Rocq Marked Regex development. *)

From Stdlib Require Import Arith List.
Import ListNotations.

(* I should use Well Founded Relations instead... *)

Theorem strong_induction_nat :
  forall P : nat -> Prop,
    (forall n, (forall k, k < n -> P k) -> P n) ->
    forall n, P n.
Proof.
  intros P. intros H.
  assert (forall n, (forall k, k < n -> P k)). 
  - intros n. induction n. 
    + intros. inversion H0.
    + intros. case (k <? n) eqn:H1. 
      * apply Nat.ltb_lt in H1. apply IHn. assumption.
      * apply H in IHn. apply Nat.ltb_ge in H1.
      assert (k=n). 
      apply Nat.le_antisymm. apply Nat.lt_succ_r. assumption. assumption.
      rewrite H2. assumption. 
  - intros n. apply (H n) in H0. assumption.
Qed.

Theorem strong_induction_list :
  forall (A : Type) (P : list A -> Prop),
  P [] -> 
  (forall l, (forall l', length l' < length l -> P l') -> P l) ->
  forall l : list A, P l.
Proof.
  intros A P Hnil Hstep l.
  (* We perform strong induction on the length of l. *)
  remember (length l) as n eqn:Hn.

  (* Define a predicate on nats that says:
       Q n := for all lists of length n, P that list.
  *)
  set (Q := fun n => forall l', length l' = n -> P l').

  (* We will prove Q n using strong_induction_nat *)
  assert (Q n) as HQ.
  {
    apply strong_induction_nat.
    intro n0.
    intros IH.                (* IH : forall k < n0, Q k *)
    unfold Q.                 (* Show: forall l', length l' = n0 -> P l' *)
    intros l' Hlen.
    destruct l' as [|x xs].
    - (* l' = [] *)
      simpl in Hlen. subst. apply Hnil.
    - (* l' = x :: xs *)
      simpl in Hlen. subst n0.
      apply Hstep.                    (* Need ∀ l'', length l'' < S (length xs) → P l'' *)
      intros l'' Hlt.
      (* Use IH on lists of smaller length *)
      apply (IH (length l'')) in Hlt. (* Hlt : length l'' < S (length xs) *)
      unfold Q in Hlt.
      apply Hlt. reflexivity.
  }

  (* Now instantiate HQ with l itself (whose length is n) *)
  unfold Q in HQ.
  apply HQ. symmetry. assumption.
Qed.

Ltac strong_induction x :=
  match type of x with
  | nat =>
      induction x using strong_induction_nat
  | list _ =>
      induction x using strong_induction_list
  end.