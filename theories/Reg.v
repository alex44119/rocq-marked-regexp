(** * Regular Expressions (Reg)
    Following the notations and structure from:
    "A Play on Regular Expressions" — Fischer, Huch, and Wilke (ICFP 2010).
*)

From Stdlib Require Import String Ascii.

(* Regular expressions *)
Inductive Reg : Type :=
| Eps : Reg                           (* ε *)
| Sym : Ascii.ascii -> Reg            (* a *)
| Alt : Reg -> Reg -> Reg             (* α | β *)
| Seq : Reg -> Reg -> Reg             (* α β *)
| Rep : Reg -> Reg.                   (* α* *)
