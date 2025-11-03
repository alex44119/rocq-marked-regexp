(** * Regular Expressions (Reg)
    Following the notations and structure from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

(* Regular expressions *)
Inductive Reg (A : Type) : Type :=
| Eps : Reg A                           (* ε *)
| Sym : A -> Reg A            (* a *)
| Alt : Reg A -> Reg A -> Reg A             (* α | β *)
| Seq : Reg A -> Reg A -> Reg A             (* α β *)
| Rep : Reg A -> Reg A.                   (* α* *)
