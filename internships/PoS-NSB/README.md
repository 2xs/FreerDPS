This folder presents the work of Awshan Hussain during his internship in the 2xs team.

This work is based on [Formalizing Nakamoto-Style Proof-of-Stake](https://arxiv.org/pdf/2007.12105) and a fork of [https://github.com/AU-COBRA/PoS-NSB](https://github.com/AU-COBRA/PoS-NSB).

The objective of this internship was to formalize the probabilistic bounds of the 3 main theorems of the paper. This work is not finished as of yet, only Chain Growth has been finished, the other two are still work-in-progress.

As of the time of writing two files are new work :
- [Properties/Prob_Bounds.v](./Properties/Prob_Bounds.v) : Main formalization work
- [Properties/additional_lemmas.v](./Properties/additional_lemmas.v) : reusable lemmas, some do exist in mathcomp but have not been found by @Awshan, some might need to lie somewhere else.

One is not merged yet :
- [Properties/sampling.v](./Properties/sampling.v) comes from a [PR in mathcomp-analysis](https://github.com/math-comp/analysis/pull/1645), an [issue has been posted](https://github.com/math-comp/analysis/issues/2149) to ask a merge of the required lemmas.

Other files come from the base repository of @sethomsen, the few updates that were made on those files are to keep them up-to-date with the current mathcomp ecosystem. No lemma have been added nor deleted in those files.

# Formalization of PoS-NSB probabilistic bounds

This repository contains a formalization of the probabilistic bounds in
the article Formalizing Nakamoto-Style Proof-of-Stake that can be found here :

The three theorems can be found in those files :
- Properties/CG.v (for Chain Growth)
- Properties/CQ.v (for Chain Quality)
- Properties/CP.v (for Common Prefix)

## Meta

- Author(s) of the article:
  - Søren Eller Thomsen
  - Bas Spitters
- Compatible Rocq versions: 9.0.0 or later
- Additional dependencies:
  - [rocq-mathcomp-ssreflect 2.5.0](https://math-comp.github.io)
  - [rocq-mathcomp-finmap 2.2.2](https://github.com/math-comp/finmap)
  - [rocq-mathcomp-analysis 1.16.0](https://github.com/math-comp/analysis)
  - [rocq Equations 1.3.1](https://github.com/mattam82/Coq-Equations)
  - [Coq record update 0.3.6](https://github.com/tchajed/coq-record-update)
  - [rocq-hierarchy-builder 1.10.2](https://github.com/math-comp/hierarchy-builder)
- Coq namespace: `AUChain`
- Related publication(s):
  - [Formalizing Nakamoto-Style Proof of Stake](https://arxiv.org/abs/2007.12105)

## Building
The requirements can be installed via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install \
     rocq-prover.9.0.0 \
     rocq-mathcomp-ssreflect.2.5.0 \
     rocq-mathcomp-finmap \
     rocq-mathcomp-analysis \
     rocq-equations \
     coq-record-update \
     rocq-hierarchy-builder
```
Then, run `make clean; make` from the root folder. This will build all
the libraries and check all the proofs.
