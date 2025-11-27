(** * Regular Expression Accept Function (RegAccept)
    This file implements `accept` function from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import Ascii Bool List.
From MarkedRegex Require Import Reg.
Import ListNotations.

Definition split {A : Type} (l : list A) : list (list A * list A) :=
  let f := (fun (x : nat) => (firstn x l, skipn x l)) in
    map f (seq 0 ((length l)+1)).

(* Eval *)
Eval compute in (split []).
Eval compute in (split [1;2;3]).

Fixpoint parts {A : Type} (l : list A) : list (list (list A)) :=
  match l with
  | [] => [[]]   (* la seule partition de la liste vide *)
  | [c] => [[[c]]] (* une seule partition pour singleton *)
  | c::cs =>
      let pss := parts cs in
      concat (map (fun ps =>
        match ps with
        | [] => []  (* impossible, devrait pas arriver *)
        | p :: ps' =>
            [ (c :: p) :: ps'; [ [c] ] ++ (p :: ps') ]  (* 2 façons *)
        end
      ) pss)
  end.


(* Eval *)
Eval compute in (parts []).
Eval compute in (parts [1]).


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
      existsb (fun '(w1,w2) => accept eqA r1 w1 && accept eqA r2 w2) (split w)
  | Rep r' =>
      (* tester toutes les partitions *)
      existsb (fun ws => forallb (fun wi => accept eqA r' wi) ws) (parts w)
  end.


(* 
Definition sigma_accept_Eps {A : Type} (w : list A)
  : { language_of (Eps A) w } + { ~ language_of (Eps A) w }.
Proof.
  destruct w as [| a w'].
  - simpl. left. reflexivity.
  - simpl. right. intros H. discriminate H.
Qed.


Fixpoint sigma_accept {A : Type} (eqA : A -> A -> bool) (r : Reg A) (w : list A)
  : { language_of r w } + { ~ language_of r w } :=
  match r return { language_of r w } + { ~ language_of r w } with
  | Eps _ => sigma_accept_Eps w'
  | 
  end. *)
