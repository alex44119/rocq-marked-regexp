(** * Regular Expression Accept Function (RegAccept)
    This file implements `accept` function from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import Ascii Bool List Arith Nat Lia BinPos BinNat ProofIrrelevance.
From MarkedRegex Require Import Reg Util.
Import ListNotations. 

Section DefSplit.

  Context {A : Type}.

  Definition valid_split (l : list A) :=
    { lr : list A * list A |
      fst lr ++ snd lr = l }.

  Definition f_split (l : list A) (x : nat)
    : valid_split l := (exist (fun lr => fst lr ++ snd lr = l) 
    (firstn x l, skipn x l)
    (firstn_skipn x l)).

  Definition splits_result (l : list A) := 
    { result : list (valid_split l) |
      forall x : (valid_split l), In x result}.

  Definition splits (l : list A) : splits_result l.
  Proof.
    refine (exist _ (map (f_split l) (seq 0 (length l + 1))) _).
    intros. apply in_map_iff. destruct x. exists (length (fst x)).
    split.
    - apply (sig_proof_irrelevance _ _ proof_irrelevance). simpl.
      replace l with (fst x ++ snd x).
      rewrite firstn_length_concat, skipn_length_concat. 
      destruct x. simpl. reflexivity.
    - subst l.
      rewrite in_seq.
      split.
      + lia.
      + rewrite length_app. lia.
  Defined.

End DefSplit.

Section DefParts.

  Context {A : Type}.

  Definition valid_ps (l : list A) :=
    { part : list (list A) |
      concat part = l /\
      Forall (fun p => p <> []) part }.

  Definition ps_empty : valid_ps [].
  Proof.
    refine (exist _ [] _).
    split. reflexivity. apply Forall_nil.
  Defined.

  Definition ps_singleton (e : A) : valid_ps [e].
  Proof.
    refine (exist _ [[e]] _).
    split. reflexivity. constructor. compute. intros. inversion H. apply Forall_nil.
  Defined.

  Definition add_in (l : list A) (e : A) (ps : valid_ps l) : 
            valid_ps (e :: l).
  Proof.
    destruct ps as [part Hvalid].
    case part as [| h t]. 

    - destruct Hvalid. rewrite concat_nil in H. rewrite <- H.  
      refine (ps_singleton e).
    - (* Case part = h :: t *)
      refine (exist _ ((e :: h) :: t) _).
      destruct Hvalid. rewrite Forall_cons_iff in H0. destruct H0.
      split.
      + rewrite concat_cons. rewrite concat_cons in H. rewrite <- app_comm_cons. 
      rewrite H. reflexivity.
      + rewrite Forall_cons_iff. split.
        * compute. intros. inversion H2.
        * apply H1.
  Defined.

  Definition add_out (l : list A) (e : A) (ps : valid_ps l) : 
        valid_ps (e :: l).
  Proof.
    destruct ps as [part Hvalid].
    case part as [| h t]. 

    - (* Case part = [] *)
      refine (exist _ [[e]] _).
      destruct Hvalid. split.
      + rewrite concat_nil in H. rewrite <- H. simpl. reflexivity.
      + constructor. compute. intros. inversion H1. apply Forall_nil.
    - (* Case part = h :: t *)
      refine (exist _ ([e] :: (h :: t)) _).
      destruct Hvalid. rewrite Forall_cons_iff in H0. destruct H0.
      split.
      + rewrite concat_cons. rewrite H. simpl. reflexivity.
      + rewrite Forall_cons_iff. split.
        * compute. intros. inversion H2.
        * rewrite Forall_cons_iff. split. apply H0. apply H1.
  Defined.

  Lemma back_parts (h : A) (t : list A) (ps : valid_ps (h::t)) :
            (exists ps' : (valid_ps t), ps = add_in t h ps')
            \/
            (exists ps' : (valid_ps t), ps = add_out t h ps').
  Proof.
    destruct ps as [part [Hconcat Hforall]].
    destruct part as [| p rest].
    - (* impossible: concat [] ≠ h :: t *)
      simpl in Hconcat. discriminate.

    - destruct p as [| a p'].
      + (* impossible: empty block *)
        simpl in Hforall.
        inversion Hforall; contradiction.

      + simpl in Hconcat.
        inversion Hconcat; subst a.

        destruct p' as [| x xs].
        * (* p = [h] : add_out case *)
          right. 
          assert (Forall (fun p : list A => p <> []) ([h] :: rest)) by exact Hforall.
          rewrite Forall_cons_iff in H. destruct H. clear H. simpl in H1.
          refine (ex_intro _ _ _).
          apply (sig_proof_irrelevance _ _ proof_irrelevance).
          simpl. clear Hconcat.
          instantiate (1 := (exist _ rest (conj H1 H0))).
          destruct rest.
          compute. reflexivity.
          compute. reflexivity.

        * (* p = h :: _ : add_in case *)
          left. assert (Forall (fun p : list A => p <> []) ((x :: xs) :: rest)).
          rewrite Forall_cons_iff in Hforall. destruct Hforall.
          rewrite Forall_cons_iff. split. symmetry. apply nil_cons. apply H0.
          rewrite <- concat_cons in H1.
          refine (ex_intro _ _ _).
          apply (sig_proof_irrelevance _ _ proof_irrelevance).
          simpl. 
          instantiate (1 := (exist _ ((x :: xs) :: rest) (conj H1 H))).
          destruct rest.
          compute. reflexivity.
          compute. reflexivity.
  Qed.

  Definition parts_result (l : list A) := 
    { result : list (valid_ps l) |
      forall x : (valid_ps l), In x result}.

  Definition extend (e : A) (l : list A) (result : parts_result l) :
    parts_result (e :: l).
  Proof.
    destruct l as [| h].
    - intros. refine (exist _ [ps_singleton e] _).
      intros. simpl. left. destruct x as [part [Hconcat Hforall]].
      apply (sig_proof_irrelevance _ _ proof_irrelevance).
      simpl. symmetry. apply partition_of_singleton_is_singleton; assumption.
    - refine (exist _ 
    ((map (add_in (h :: l) e) (proj1_sig result)) 
    ++ (map (add_out (h :: l) e) (proj1_sig result))) _). intros ps.
    pose proof (back_parts e (h::l) ps).
    destruct H as [[x H]|[x H]]. 
      + destruct result as [result P]. pose proof (P x).
      apply in_or_app. left. simpl. rewrite in_map_iff.
      exists x. split.
        * rewrite H. reflexivity.
        * apply H0.
      + destruct result as [result P]. pose proof (P x).
      apply in_or_app. right. simpl. rewrite in_map_iff.
      exists x. split.
        * rewrite H. reflexivity.
        * apply H0.
  Qed.

  Definition parts_result_empty : parts_result [].
  Proof.
    refine (exist _ [ps_empty] _).
    intros. destruct x as [x [a H]]. simpl.
    pose proof ((proj1 (concat_nil_Forall x)) a).
    pose proof (forall_false_nil x (fun a => a = [])) H0 H.
    left. apply (sig_proof_irrelevance _ _ proof_irrelevance).
    simpl. symmetry. apply H1.
  Qed.

  Fixpoint parts (l : list A) : parts_result l :=
    match l with 
      |[] => parts_result_empty
      |h::t => let prec_parts := parts t in extend h t prec_parts
      end.

End DefParts.

Section RegAccept.

  Context {A : Type}.

  Parameter EqDec : forall x y : A, {x = y} + {x <> y}.

  Definition eqb (x y : A) : bool :=
    if EqDec x y then true else false.

  Lemma eqb_true_iff
     : forall a b : A, eqb a b = true <-> a = b.
  Proof.
    intros. split.
    - compute. destruct (EqDec a b); auto. intros. inversion H.
    - intro H. rewrite H. compute. destruct (EqDec b b). reflexivity. 
    compute in n. assert (b = b). reflexivity. pose proof (n H0). inversion H1.
  Qed.

  Infix "=?":= eqb (at level 70).

  Fixpoint acceptb (r : Reg) (w : list A) : bool :=
    match r with
    | Eps =>
        match w with
        | [] => true
        | _  => false
        end

    | Sym a =>
        match w with
        | [b] => a =? b
        | _   => false
        end

    | Alt r1 r2 =>
        acceptb r1 w || acceptb r2 w

    | Seq r1 r2 =>
        let ss := proj1_sig (splits w) in
        existsb
          (fun s =>
             let '(w1, w2) := proj1_sig s in
             acceptb r1 w1 && acceptb r2 w2)
          ss

    | Rep r' =>
        let ps := proj1_sig (parts w) in
        existsb
          (fun p =>
             let ws := proj1_sig p in
             forallb (fun wi => acceptb r' wi) ws)
          ps
    end.

End RegAccept.