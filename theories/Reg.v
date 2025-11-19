(** * Regular Expressions (Reg)
    Following the notations and structure from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import List Lia Program.Equality.
From MarkedRegex Require Import Util.
Import ListNotations.

Section RegDef.
(** * Definition of Reg

    This sections defines  inductive Reg type presented in the paper *)

    Context {A : Type}.

(** Polymorphic regular expressions *)
Inductive Reg : Type :=
| Eps : Reg                     (* ε *)
| Sym : A -> Reg                (* a *)
| Alt : Reg -> Reg -> Reg       (* α | β *)
| Seq : Reg -> Reg -> Reg       (* α β *)
| Rep : Reg -> Reg.             (* α* *)

End RegDef.

Section Semantics.
  (** * Definitions of language_of

    This sections defines the semantical function
    language_of : forall (A : Type), Reg A -> list A -> Prop 
    in two ways, first one is using Fixpoint and the other one uses Inductive *)

    Context {A : Type}.

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
| LangEps : forall w, w = [] -> language_of_ind Eps w
| LangSym : forall a, language_of_ind (Sym a) [a]
| LangAltL : forall r1 r2 w, language_of_ind r1 w -> language_of_ind (Alt r1 r2) w
| LangAltR : forall r1 r2 w, language_of_ind r2 w -> language_of_ind (Alt r1 r2) w
| LangSeq : forall r1 r2 w1 w2,
    language_of_ind r1 w1 ->
    language_of_ind r2 w2 ->
    language_of_ind (Seq r1 r2) (w1 ++ w2)
| LangRep0 : forall r, language_of_ind (Rep r) []
| LangRepStep : forall r w1 w2,
    w1 <> [] -> language_of_ind r w1 ->
    language_of_ind (Rep r) w2 ->
    language_of_ind (Rep r) (w1 ++ w2).

End Semantics.

Section Equivalence.
  (** * Equivalence of these two definitions

    In this section, we prove that language_of and language_of_ind are equivalent. *)

    Context {A : Type}.

Proposition language_of_to_ind :  
  forall (r : Reg) (w : list A),
    language_of r w -> language_of_ind r w.
Proof.
  intros r. induction r.
  - intros. unfold language_of in H. rewrite H. apply LangEps. reflexivity.
  - intros. unfold language_of in H. rewrite H. apply LangSym.
  - intros. destruct H.
    * apply LangAltL. apply IHr1. assumption.
    * apply LangAltR. apply IHr2. assumption.
- intros. destruct H as [l1 [l2 [concat [H H']]]].
    apply IHr1 in H. apply IHr2 in H'. 
    rewrite concat. apply LangSeq. 
    assumption. assumption. 
  - intros. destruct H as [x [H]]. rewrite <- H. clear H w. 
  induction x.
    * rewrite concat_nil. apply LangRep0.
    * pose proof ((IHr a) ((H0 a) (in_eq a x))). 
    assert (forall wi : list A, In wi x -> language_of r wi).
      + intros. pose proof ((H0 wi) ((in_cons a wi x) H1)). assumption.
      + pose proof (IHx H1). clear IHx H1. destruct a.
       -- assumption.
       -- assert ([] <> a :: a0) as Hnil by (apply nil_cons).
          apply ((LangRepStep r (a::a0) (concat x)) (not_eq_sym Hnil) H H2).
Qed.


Lemma language_of_to_fix :
  forall (r : Reg) (w : list A),
    language_of_ind r w -> language_of r w.
Proof.
  intros r. induction r. 
  - intros. dependent destruction H. assumption.
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
    + dependent destruction H.
      * exists []. split.
        -- apply concat_nil.
        -- intros. inversion H.
      * rewrite <- length_zero_iff_nil in H. apply not_eq_sym in H.
        apply (Arith_base.neq_0_lt_stt (Datatypes.length w1)) in H.
        assert (length w2 < length w1 + length w2) by lia. rewrite <- (length_app w1 w2) in H3.
        pose proof (H0 w2 H3 H2). destruct H4. exists (w1 :: x). split.
        -- rewrite concat_cons. destruct H4. rewrite H4. reflexivity. 
        -- destruct H4. intros. destruct H6.
          ++ rewrite <- H6. apply H1.
          ++ apply (H5 wi H6).
    + simpl. repeat destruct H0. clear H. exists x. split. reflexivity. intros. 
    apply ((IHr wi) (H1 wi H)).
Qed.

Theorem language_of_equiv :
  forall (r : Reg) (w : list A),
    language_of r w <-> language_of_ind r w.
Proof.
  intros r w. split.
  - apply language_of_to_ind.
  - apply language_of_to_fix.
Qed.

End Equivalence.