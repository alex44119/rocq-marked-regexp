(** * Regular Expression Accept Function (RegAccept)
    This file implements `accept` function from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import String Ascii Bool List.
From MarkedRegex Require Import Reg.
Import ListNotations.

Fixpoint split {A : Type} (l : list A) : list (list A * list A) :=
  match l with
  | [] => [([],[])]
  | c :: cs =>
      let rest := split cs in
      ([], c::cs) :: map (fun '(s1,s2) => (c::s1, s2)) rest
  end.

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

Fixpoint accept {A : Type} (eqA : A -> A -> bool) (r : Reg A) (w : list A) : bool :=
  match r with
  | Eps _ => match w with [] => true | _ => false end
  | Sym _ a => match w with [b] => eqA a b | _ => false end
  | Alt _ r1 r2 => accept eqA r1 w || accept eqA r2 w
  | Seq _ r1 r2 =>
      (* tester toutes les décompositions *)
      existsb (fun '(w1,w2) => accept eqA r1 w1 && accept eqA r2 w2) (split w)
  | Rep _ r' =>
      (* tester toutes les partitions *)
      existsb (fun ws => forallb (fun wi => accept eqA r' wi) ws) (parts w)
  end.