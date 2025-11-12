(** * Regular Expressions (Reg)
    Following the notations and structure from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import String List Ascii Nat Program.Wf Lia.
Import ListNotations.

(** Polymorphic regular expressions *)
Inductive Reg (A : Type) : Type :=
| Eps : Reg A                         (* ε *)
| Sym : A -> Reg A                    (* a *)
| Alt : Reg A -> Reg A -> Reg A       (* α | β *)
| Seq : Reg A -> Reg A -> Reg A       (* α β *)
| Rep : Reg A -> Reg A.               (* α* *)

Definition RegChar := Reg Ascii.ascii.
Definition RegBool := Reg bool.

(* Inductive version *)
Inductive language_of {A : Type} : Reg A -> list A -> Prop :=
| LangEps : forall w, w = [] -> language_of (Eps A) w
| LangSym : forall a, language_of (Sym A a) [a]
| LangAltL : forall r1 r2 w, language_of r1 w -> language_of (Alt A r1 r2) w
| LangAltR : forall r1 r2 w, language_of r2 w -> language_of (Alt A r1 r2) w
| LangSeq : forall r1 r2 w1 w2,
    language_of r1 w1 ->
    language_of r2 w2 ->
    language_of (Seq A r1 r2) (w1 ++ w2)
| LangRep0 : forall r, language_of (Rep A r) []
| LangRepStep : forall r w1 w2,
    w1 <> [] ->
    language_of r w1 ->
    language_of (Rep A r) w2 ->
    language_of (Rep A r) (w1 ++ w2).


(* Fixpoint version : doesn't work yet *)
(* Fixpoint size {A : Type} (r : Reg A) : nat :=
  match r with
  | Eps _ => 1
  | Sym _ _ => 1
  | Alt _ r1 r2 => 1 + size r1 + size r2
  | Seq _ r1 r2 => 1 + size r1 + size r2
  | Rep _ r' => 1 + size r'
  end.

Definition measure {A : Type} (p : Reg A * list A) : nat :=
  size (fst p) + length (snd p).

Program Fixpoint language_of {A : Type} (r : Reg A) (w : list A) {measure (size r + length w)} : Prop :=
  match r, w with
  | Eps _, _ => w = []
  | Sym _ a, _ => w = [a]
  | Alt _ r1 r2, _ => language_of r1 w \/ language_of r2 w
  | Seq _ r1 r2, _ =>
      exists w1 w2, w = w1 ++ w2 /\ language_of r1 w1 /\ language_of r2 w2
  | Rep _ r', _ =>
      w = [] \/
      exists w1 w2,
        w = w1 ++ w2 /\
        w1 <> [] /\
        language_of r' w1 /\
        language_of r w2
  end.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation.
simpl.
lia.
Qed.
Next Obligation. *)

