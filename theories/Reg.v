(** * Regular Expressions (Reg)
    Following the notations and structure from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import List Lia Program.Equality.
From MarkedRegex Require Import Util.
Import ListNotations.

Section RegularExpressions.

  Context {A : Type}.

(** * Polymorphic regular expressions *)

  Inductive Reg : Type :=
    | Eps : Reg                     (* ε *)
    | Sym : A -> Reg                (* a *)
    | Alt : Reg -> Reg -> Reg       (* α | β *)
    | Seq : Reg -> Reg -> Reg       (* α β *)
    | Rep : Reg -> Reg.             (* α* *)


(** * Fixpoint Semantics *)

  Fixpoint language_of (r : Reg) (w : list A) : Prop :=
    match r with
    | Eps => w = []
    | Sym a => w = [a]
    | Alt r1 r2 => language_of r1 w \/ language_of r2 w
    | Seq r1 r2 =>
        exists w1 w2,
          w = w1 ++ w2 /\
          language_of r1 w1 /\
          language_of r2 w2
    | Rep r' =>
        exists (ws : list (list A)),
          concat ws = w /\
          (forall wi, In wi ws -> language_of r' wi)
    end.

Inductive language_of_ind : Reg -> list A -> Prop :=
| LangEps : language_of_ind Eps []
| LangSym : forall a, language_of_ind (Sym a) [a]
| LangAltL : forall r1 r2 w, language_of_ind r1 w -> language_of_ind (Alt r1 r2) w
| LangAltR : forall r1 r2 w, language_of_ind r2 w -> language_of_ind (Alt r1 r2) w
| LangSeq : forall r1 r2 w1 w2,
    language_of_ind r1 w1 ->
    language_of_ind r2 w2 ->
    language_of_ind (Seq r1 r2) (w1 ++ w2)
| LangRep0 : forall r, language_of_ind (Rep r) []
| LangRepStep : forall r w1 w2,
    language_of_ind r w1 ->
    language_of_ind (Rep r) w2 ->
    language_of_ind (Rep r) (w1 ++ w2).


(** * Equivalence of these two definitions *)

Proposition language_of_fix_to_ind :  
  forall (r : Reg) (w : list A),
    language_of r w -> language_of_ind r w.
Proof.
  intros r. induction r.
  - intros. unfold language_of in H. rewrite H. apply LangEps.
  - intros. unfold language_of in H. rewrite H. apply LangSym.
  - intros. destruct H.
    * apply LangAltL. apply IHr1. assumption.
    * apply LangAltR. apply IHr2. assumption.
  - intros. destruct H as [l1 [l2 [concat [H H']]]].
    apply IHr1 in H. apply IHr2 in H'. 
    rewrite concat. apply LangSeq. 
    assumption. assumption. 
  - intros. destruct H as [x [H]]. rewrite <- H. clear H w. 
    induction x as [H|a l].
    * rewrite concat_nil. apply LangRep0.
    * simpl; apply LangRepStep.
      + apply IHr; apply H0; left; reflexivity.
      + apply IHl.
        intros wi Hwi.
        apply H0; right; assumption.
Qed.

Lemma language_of_ind_Rep_exists' :
forall r (w : list A), language_of_ind r w ->
 forall r', r = Rep r' ->
  w <> [] ->
  exists w1 w2, w = w1 ++ w2 /\ w1 <> [] /\ language_of_ind r' w1 /\ language_of_ind (Rep r') w2.
Proof.
induction 1; intros; try discriminate.
- contradict H0; reflexivity.
- inversion H1; subst.
  destruct w1.
  * assert (Heq: Rep r' = Rep r') by auto.
    specialize (IHlanguage_of_ind2 _ Heq H2).
    assumption.
  * exists (a::w1), w2.
    split; try reflexivity.
    split; try discriminate.
    split; assumption.
Qed.

Lemma language_of_ind_Rep_exists :
forall r (w : list A), language_of_ind (Rep r) w ->
  w <> [] ->
  exists w1 w2, w = w1 ++ w2 /\ w1 <> [] /\ language_of_ind r w1 /\ language_of_ind (Rep r) w2.
Proof.
intros; eapply language_of_ind_Rep_exists'; eauto.
Qed.

Lemma language_of_ind_to_fix :
  forall (r : Reg) (w : list A),
    language_of_ind r w -> language_of r w.
Proof.
  intros r. induction r. 
  - intros. inversion H; subst. reflexivity.
  - intros. dependent destruction H. simpl. reflexivity.
  - intros. dependent destruction H. simpl. 
      left.  apply ((IHr1 w) H).
      right. apply ((IHr2 w) H).
  - intros. dependent destruction H. simpl. exists w1. exists w2. repeat split.
    + apply ((IHr1 w1) H).
    + apply ((IHr2 w2) H0).
  - intros. assert (exists (ws : list (list A)),
        concat ws = w /\ (forall wi, In wi ws -> language_of_ind r wi)).
  strong_induction w.
    + exists []. split.
      * apply concat_nil.
      * intros. inversion H0.
    + destruct w.
      * exists []. split.
        -- apply concat_nil.
        -- intros; inversion H1.
      * assert (Haw: a :: w <> []) by auto with datatypes.
        pose proof (language_of_ind_Rep_exists _ _ H Haw)
         as [w1 [w2 [Heq [Hneq [Hw Hw']]]]].
        assert (Hw2: length w2 < length (a :: w)). {
          destruct w1.
          - contradict Hneq; reflexivity.
          - simpl in Heq.
            inversion Heq; subst.
            simpl.
            rewrite length_app.
            lia.
        }
        pose proof (H0 w2 Hw2 Hw') as [ws [Hws]].
        rewrite Heq.
        exists (w1 :: ws).
        simpl.
        rewrite Hws.
        split; [reflexivity|].
        intros wi Hin.
        destruct Hin.
        -- rewrite <- H2; assumption.
        -- apply H1; assumption.
    + simpl. repeat destruct H0. clear H. exists x. split. reflexivity. intros. 
      apply ((IHr wi) (H1 wi H)).
Qed.

Theorem language_of_equiv :
  forall (r : Reg) (w : list A),
    language_of r w <-> language_of_ind r w.
Proof.
  intros r w. split.
  - apply language_of_fix_to_ind.
  - apply language_of_ind_to_fix.
Qed.

End RegularExpressions.