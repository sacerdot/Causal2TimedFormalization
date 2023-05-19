# Causal2TimedFormalization
Sources for the formalization in Matita of the implication between causal reversibility and time reversibility.

The repository contains the formalization of the main theorem presented in the paper ``Causal Reversibility Implies Time Reversibility''
submitted at QEST 2023.

## Structure of the repository

The repository contains the following files:

- formalization.pdf: a PDF file relating the definitions and theorems in the
  paper with those in the formalization
- causal2timed.ma: it caontins all the definitions and proofs in the paper
  require for Theorem 2, which is the main result
  of the paper that is formalized in Matita
- z_axioms.ma: the previous file depends on this one that provides an axiomatization of integer numbers
- z.ma: this file shows a model of the axioms in z_axioms.ma (or, equivalently, an implementation of integer numbers that
  satisfy the axiomatization given in z_axioms and used in the proof)
- complements.ma: it contains some facts not necessary for the main proof; the file is not required by causal2timed.ma

## How to check the proof

The formalization can be checked by Matita version >= 0.99.5, that can be downloaded from [matita](https://github.com/sacerdot/matita).

The easiest way to compile matita is to setup [opam](https://opam.ocaml.org/doc/Install.html) with OCaml version 4.14.1 and then do
```opam pin .''' in the directory where you downloaded matita.

Once installed, it is sufficient to start Matita with ```matita causal2timed.ma''' and then press the ```Execute all''' button to verify
everything in the main file and in the ones included by it.
