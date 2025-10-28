# Marked Regular Expressions in Coq/Rocq

## Description
The project formalizes a variant of regular expressions in Coq (Rocq), following the paper  
[*A Play on Regular Expressions* by Fischer, Huch, and Wilke (ICFP 2010)](http://sebfisch.github.io/haskell-regexp/regexp-play.pdf).

It includes:
- A Coq model of regular expressions (`Reg`), marked (`MReg`), and cached (`CMReg`) versions.
- Verified properties such as correctness of the matcher.
- Extraction of verified OCaml code for matching strings.

## Tools
- [Coq / Rocq](https://coq.inria.fr/)
- OCaml (for extracted code)

## License
This project is licensed under the [MIT License](LICENSE).

© 2025 Alex Martinez Rivera
