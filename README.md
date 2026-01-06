# Marked Regular Expressions in Coq/Rocq

## Description
The project formalizes a variant of regular expressions in Coq (Rocq), following the paper  
[*A Play on Regular Expressions* by Fischer, Huch, and Wilke (ICFP 2010)](http://sebfisch.github.io/haskell-regexp/regexp-play.pdf).

It includes:
- A Coq model of regular expressions (`Reg`), marked (`MReg`), and cached (`CMReg`) versions.
- Verified properties such as correctness of the matcher.
- Extraction of verified OCaml code for matching strings.

## Reproducibility

### Environment

- **OCaml version:** 4.14.0
- **Rocq version:** 9.0.0
- **Opam version:** 2.3.0
- **VS Code extension:** VSRocq (v2.3.2)
- **Makefile:** GNUMakefile for Rocq 9.0.0 

```bash
$ rocq --version
The Rocq Prover, version 9.0.0
compiled with OCaml 4.14.0
$ opam --version
2.3.0
```

### Verification

After running `make`, the build should finish without errors.

Expected output (ending lines):

```bash
$ make
rocq makefile -f _CoqProject -o Makefile.rocq
ROCQ DEP VFILES
ROCQ compile theories/Util.v
ROCQ compile theories/Reg.v
ROCQ compile theories/RegAccept.v
```

## Tools
- [Coq / Rocq](https://coq.inria.fr/)
- OCaml (for extracted code)

## License
This project is licensed under the [MIT License](LICENSE).

© 2025 Alex Martinez Rivera
