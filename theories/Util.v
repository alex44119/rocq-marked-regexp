(** * Utilities for proofs and tactics
    This file contains helper tactics and common utilities used across
    the Rocq Marked Regex development. *)

From Stdlib Require Import Bool List Arith Nat Lia.
Import ListNotations.

  (* ------------------------------------------------------------ *)
  (*                 strong_induction tactic                      *)
  (* ------------------------------------------------------------ *)

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


  (* ------------------------------------------------------------ *)
  (*             useful lemmas that should be standard            *)
  (* ------------------------------------------------------------ *)

Lemma firstn_length_concat : forall (A : Type) (w1 w2 : list A),
  firstn (length w1) (w1 ++ w2) = w1.
Proof.
  intros.
  rewrite firstn_app.
  replace (length w1 - length w1) with 0 by lia.
  rewrite firstn_all. simpl. apply app_nil_r.
Qed.

Lemma skipn_length_concat : forall (A : Type) (w1 w2 : list A),
  skipn (length w1) (w1 ++ w2) = w2.
Proof.
  intros A w1 w2.
  induction w1 as [|x w1' IH].
    simpl.
    reflexivity.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma forall_false_nil {A : Type} (l : list A) (P : A -> Prop) 
  (H1 : Forall (fun x : A => P x) l)
  (H2 : Forall (fun x : A => P x -> False) l) : l = [].
Proof.
  destruct l as [| x xs].
  - reflexivity.
  - inversion H1 as [| ? ? HP H1'].
    inversion H2 as [| ? ? HnotP H2'].
    exfalso.
    apply HnotP.
    exact HP.
Qed.

Lemma partition_of_singleton_is_singleton
      {A : Type} (e : A) (part : list (list A)) :
  concat part = [e] ->
  Forall (fun p : list A => p <> []) part ->
  part = [[e]].
Proof.
  intros Hconcat Hforall.
  destruct part as [|p part'].
  - (* part = [] : impossible because concat [] = [] <> [e] *)
    simpl in Hconcat. discriminate.
  - (* part = p :: part' *)
    destruct part' as [|p' part''].
    + (* part = [p], and concat [p] = p *)
      simpl in Hconcat.                    (* Hconcat : p = [e] *)
      rewrite app_nil_r in Hconcat.
      subst p. reflexivity.                (* part = [[e]] *)
    + (* part has at least two blocks, all non-empty: impossible *)
      inversion Hforall as [| ? ? Hp_nonempty Hforall'].
      inversion Hforall' as [| ? ? Hp'_nonempty _].
      destruct p as [|a p_tail].
      * assert (([] : list A) = ([] : list A)) by reflexivity. exfalso. apply (Hp_nonempty H3).
      * destruct p' as [|b p'_tail].
        -- (* p' = [] contradicts Hp'_nonempty *)
           assert (([] : list A) = ([] : list A)) by reflexivity. exfalso. apply (Hp'_nonempty H3).
        -- (* now concat is a list with at least two elements, can't be [e] *)
           simpl in Hconcat.
           inversion Hconcat. destruct p_tail.
            --- simpl in H5. discriminate.
            --- simpl in H5. discriminate.
Qed.  

Lemma sig_proof_irrelevance
  (A : Type) (P : A -> Prop)
  (PI : forall (Q : Prop) (p1 p2 : Q), p1 = p2)
  (sig1 sig2 : { x : A | P x }) :
  proj1_sig sig1 = proj1_sig sig2 ->
  sig1 = sig2.
Proof.
  destruct sig1 as [x px].
  destruct sig2 as [y py].
  simpl.
  intro H.
  subst y.
  f_equal.
  apply PI.
Qed.

Fixpoint filter_clean (A : Type) (ws : list (list A)) : list (list A) :=
  match ws with
    |[] => []
    |h::t => let ws' := filter_clean A t in 
      match h with
        |[] => ws'
        |h_h::t_h => (h_h::t_h)::ws'
      end
  end.

Lemma concat_clean (A : Type) (w : list A) (ws : list (list A)) (Hws : concat ws = w):
  {ws' : list (list A) | concat ws' = w
                        /\ Forall (fun p : list A => p <> []) ws'
                        /\ Forall (fun p : list A => In p ws) ws'}.
Proof.
  refine (exist _ (filter_clean A ws) _).
  repeat split.
  - generalize w, Hws. clear w Hws.
    induction ws as [|x xs IH]; simpl in *.
    + intros. apply Hws.
    + destruct x as [|a x']; simpl.
      * intros. apply IH.
        simpl in Hws. apply Hws.
      * assert (concat xs = concat xs) by reflexivity.
        pose proof (IH (concat xs) H). clear H IH.
        rewrite H0.
        intros. apply Hws.
  - clear Hws. clear w. induction ws.
    + simpl. constructor.
    + case a. simpl. apply IHws.
      simpl. intros. constructor. discriminate. apply IHws.
  - clear Hws. clear w. induction ws.
    + simpl. constructor.
    + case a. simpl. apply Forall_impl with (P := fun p : list A => In p ws).
      intros p Hp. right; exact Hp. exact IHws.
      intros. simpl. apply Forall_cons. left ; reflexivity.
      apply Forall_impl with (P := fun p : list A => In p ws).
      intros p Hp. right; exact Hp. exact IHws.
Qed.