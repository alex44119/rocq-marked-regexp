(** * Regular Expression Accept Function (RegAccept)
    This file implements `accept` function from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import Ascii Bool List Arith Nat Lia.
From MarkedRegex Require Import Reg Util.
Import ListNotations.

Definition f_splits {A : Type} (l : list A) (x : nat)
  : list A * list A :=
  (firstn x l, skipn x l).

Definition splits {A : Type} (l : list A) : list (list A * list A) :=
  map (f_splits l) (seq 0 (length l + 1)).

Definition f_parts {A : Type} (e : A) (cpl : list (list A) * nat)
  : list (list A) * nat :=
  match cpl with
  | ([], n) =>
        ([[e]], n)
  | (t :: q, n) =>
        if Nat.even n
        then ((e :: t) :: q, Nat.div2 n)
        else ([e] :: t :: q, Nat.div2 n)
  end.

  Definition g_parts {A:Type} (l : list A) (n : nat) :=
    fst (fold_right f_parts ([], n) l).

Definition parts {A : Type} (l : list A) : list (list (list A)) :=
  map (g_parts l) (seq 0 (2 ^ (length l - 1))).

(* Eval *)
Eval compute in (parts []).
Eval compute in (parts [1;2;3]).

Section CorrectnessLemmas.

  Variable A : Type.

  (* ------------------------------------------------------------ *)
  (*                 Correctness of splits                        *)
  (* ------------------------------------------------------------ *)

  (* (w1, w2) ∈ parts w   <->   w = w1 ++ w2 *)

  Lemma splits_complete :
    forall (w w1 w2 : list A),
        w = w1 ++ w2 ->
        In (w1, w2) (splits w).
  Proof.
    intros w w1 w2 Hw.
    unfold splits.
    (* We need to find the index x = length w1 *)
    assert (Hx : firstn (length w1) w = w1 /\ skipn (length w1) w = w2).
    {
      rewrite Hw.
      split.
      - replace (length w1) with (length w1 + 0) by lia.
      rewrite firstn_app_2, firstn_0, app_nil_r. reflexivity.
      - rewrite skipn_app, Nat.sub_diag, skipn_0, skipn_all, app_nil_l. reflexivity.
    }
    destruct Hx as [Hf Hs].
    apply in_map_iff.
    exists (length w1).
    split; auto. rewrite Hw. unfold f_splits.
    rewrite skipn_app, Nat.sub_diag, skipn_0, skipn_all, app_nil_l.
    replace (length w1) with (length w1 + 0) by lia. 
    rewrite firstn_app_2, firstn_0, app_nil_r. reflexivity.
    apply in_seq.
    split. lia.
    rewrite Hw, length_app. lia.
  Qed.

  Lemma splits_sound :
    forall (w w1 w2 : list A),
       In (w1,w2) (splits w) ->
       w = w1 ++ w2.
  Proof.
    intros w w1 w2 Hin.
    unfold splits in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [x [Hx Hinx]].
    inversion Hx.
    rewrite firstn_skipn.
    reflexivity.
  Qed.

  Lemma splits_correct :
    forall (w w1 w2 : list A),
       In (w1,w2) (splits w) <-> w = w1 ++ w2.
  Proof.
    split.
    - apply splits_sound.
    - apply splits_complete.
  Qed.


  (* ------------------------------------------------------------ *)
  (*                 Correctness of parts                         *)
  (* ------------------------------------------------------------ *)

  (* ps ∈ parts w   <->  ps is a partition of w *)

  Definition partition {A : Type} (w : list A) (ps : list (list A)) : Prop :=
    concat ps = w /\ Forall (fun p => p <> []) ps.

  Lemma f_parts_preserves_nonempty :
    forall (e : A) ps n,
      Forall (fun p => p <> []) ps ->
      Forall (fun p => p <> []) (fst (f_parts e (ps, n))).
  Proof.
    intros e ps n H.
    destruct ps as [|t q].
    - simpl. constructor.
      + discriminate.
      + constructor.
    - simpl.
      destruct (Nat.even n).
      + constructor.
        * discriminate.
        * exact (Forall_inv_tail H).
      + constructor.
        * discriminate.
        * constructor; pose proof (Forall_inv H); auto.
        apply Forall_inv_tail in H; auto.
  Qed.

  Lemma f_parts_concat :
    forall (e : A) ps n,
      concat (fst (f_parts e (ps, n))) = e :: concat ps.
  Proof.
    intros e ps n.
    destruct ps as [|t q].
    - simpl. reflexivity.
    - simpl.
      destruct (Nat.even n); simpl; reflexivity.
  Qed.

  (* Helper: Generalize the concatenation property for fold_left *)
  Lemma fold_f_parts_concat_aux :
    forall (l : list A) (acc : list (list A) * nat),
      concat (fst (fold_right f_parts acc l)) = l ++ concat (fst acc).
  Proof.
    induction l as [|x l IH].
    - intros acc. simpl. reflexivity.
    - intros acc. simpl.
      remember (fold_right f_parts acc l) as res eqn:Hres.
      destruct res as [ps n].
      rewrite f_parts_concat.
      f_equal.
      rewrite <- IH.
      rewrite <- Hres.
      simpl. reflexivity.
  Qed.

  Lemma fold_f_parts_nonempty_aux :
    forall (l : list A) (acc : list (list A) * nat),
      Forall (fun p => p <> []) (fst acc) ->
      Forall (fun p => p <> []) (fst (fold_right f_parts acc l)).
  Proof.
    induction l as [|x l IH].
    - intros acc H. simpl. assumption.
    - intros acc H. simpl.
      remember (fold_right f_parts acc l) as res eqn:Hres.
      destruct res as [ps n].
      apply f_parts_preserves_nonempty.
      apply (f_equal fst) in Hres. simpl in Hres.
      rewrite Hres.
      apply IH.
      assumption.
  Qed.

  Lemma fold_f_parts_partition :
    forall (w : list A) n,
      partition w (g_parts w n).
  Proof.
    intros w n.
    unfold partition.
    split.
    - (* Concatenation *) unfold g_parts.
      rewrite fold_f_parts_concat_aux.
      simpl. rewrite app_nil_r.
      reflexivity.
    - (* Non-empty *)
      apply fold_f_parts_nonempty_aux.
      constructor.
  Qed.

  Lemma parts_sound :
    forall (w : list A) (ps : list (list A)),
      In ps (parts w) ->
      partition w ps.
  Proof.
    intros w ps Hin.
    unfold parts in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [n [Hps _]].
    subst ps.
    apply fold_f_parts_partition.
  Qed.

  Definition build_number {A} (ps : list (list A)) : nat :=
    fold_left (fun acc h => 2^(length h - 1) * (1 + 2 * acc)) (tl ps) 0.

  Eval compute in map (fun ps => g_parts (concat ps) (build_number ps)) (parts [1;2;3;4]).
  Eval compute in map (fun ps => build_number ps) (parts [1;2;3;4]).
  Eval compute in (parts [1;2;3;4]).

  Eval compute in (tail [[1];[2];[3;4]]).

  Eval compute in (tail [[1;2];[3]]).

  Lemma build_number_lemma:
    forall (w : list A) (ps : list (list A)),
      ps <> [] ->
      partition w ps ->
      g_parts w (build_number ps) = ps.
    Proof.
    Admitted.


  Eval compute in map (fun ps => fst (fold_right f_parts ([], (build_number ps)) (concat ps))) (parts [1;2;3]).
  Eval compute in (parts [1;2;3]).



  Lemma parts_complete :
    forall (w : list A) (ps : list (list A)),
        partition w ps ->
        In ps (parts w).
  Proof.
  Admitted.

End CorrectnessLemmas.



Fixpoint accept {A : Type} (eqA : A -> A -> bool) (r : Reg) (w : list A) : bool :=
  match r with
  | Eps => match w with 
    |[] => true
    | _ => false 
  end
  | Sym a => match w with 
    |[b] => eqA a b 
    | _  => false 
  end
  | Alt r1 r2 => accept eqA r1 w || accept eqA r2 w
  | Seq r1 r2 =>
      (* tester toutes les décompositions *)
      existsb (fun '(w1,w2) => accept eqA r1 w1 && accept eqA r2 w2) (splits w)
  | Rep r' =>
      (* tester toutes les partitions *)
      existsb (fun ws => forallb (fun wi => accept eqA r' wi) ws) (parts w)
  end.

