# Static Overload Resolution and Monomorphization for Functional Languages

[![Preprint](https://img.shields.io/badge/Preprint-PDF-red.svg)](paper.pdf)
[![Coq/Rocq](https://img.shields.io/badge/Mechanization-Coq%20%2F%20Rocq-blue.svg)](meta-theory/LangD/)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22917622.svg)](https://doi.org/10.5281/zenodo.22917622)

**Author:** Thomas Vergne  
**Preprint:** [paper.pdf](paper.pdf)  
**Zenodo Archive & DOI:** [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22917622.svg)](https://doi.org/10.5281/zenodo.22917622) [`10.5281/zenodo.22917622`](https://doi.org/10.5281/zenodo.22917622)
**Contact:** `contact@thomas-vergne.fr`

---

## Overview

This repository hosts the PDF output paper and the mechanized Coq/Rocq metatheory for the paper:
> **"Static Overload Resolution and Monomorphization for Functional Languages"**

Managing function overloading in statically typed functional programming has traditionally relied on either **dictionary passing** (e.g., Haskell type classes) with runtime overhead, or **informal static resolution heuristics** lacking metatheoretical safety proofs (e.g., C++ ad-hoc overloading).

We propose a formal compilation framework based on:
1. **Surface Calculus $\lambda_{\mathcal{O}}$**: An extension of the explicitly typed $\lambda$-calculus equipped with local property declarations ($\mathbf{prop}\ f [\vec{\alpha}] : \tau_1\ \mathbf{in}\ e_2$) and explicit overloaded call sites ($\mathbf{ext}\ f [\vec{\tau}]$).
2. **Deterministic Resolution under $\mathtt{WFC}$**: A deterministic selection of the most specific implementation ($\mathtt{MSC}$) under a syntactic well-formedness catalog condition ($\mathtt{WFC}$).
3. **Global Monomorphization**: An inductive elaboration relation $\Omega \vdash e \hookrightarrow e_m$ that eliminates all ad-hoc overloading and compiles source programs into a clean target calculus $\lambda_{\mathcal{M}}$ free of dictionaries and virtual tables.
4. **Machine-Checked Safety**: Full formalization in Coq/Rocq establishing type uniqueness, type preservation under elaboration, forward semantic simulation, and end-to-end soundness without non-standard axioms.

---

## Key Theoretical Results & Coq Mapping

The table below maps each theorem presented in the paper to its mechanized counterpart in `meta-theory/LangD/`:

| Paper Result | Informal Statement | Coq File & Lemma |
| :--- | :--- | :--- |
| **Theorem 1** | *Expression Progression ($\lambda_{\mathcal{O}}$)* | [`Typing.v`](meta-theory/LangD/Typing.v): `soundness` |
| **Theorem 2** | *Type Preservation by Reduction ($\lambda_{\mathcal{O}}$)* | [`Typing.v`](meta-theory/LangD/Typing.v): `type_preservation` |
| **Theorem 3** | *Type System Soundness ($\lambda_{\mathcal{O}}$)* | [`Typing.v`](meta-theory/LangD/Typing.v): `soundness_theoritical` |
| **Theorem 4** | *Type Uniqueness ($\lambda_{\mathcal{O}}$)* | [`Typing.v`](meta-theory/LangD/Typing.v): `type_uniqueness` |
| **Lemma 8** | *Conformance implies Environment Match* | [`Definitions.v`](meta-theory/LangD/Definitions.v): `catalog_conforms_implies_matches` |
| **Lemma 10** | *Existence of Most Specific Candidate ($\mathtt{MSC}$)* | [`Proofs.v`](meta-theory/LangD/Proofs.v): `msc_existence` |
| **Theorem 5** | *Deterministic Selection under $\mathtt{WFC}$* | [`Proofs.v`](meta-theory/LangD/Proofs.v): `deterministic_selection` |
| **Theorem 7** | *Target Progression and Preservation ($\lambda_{\mathcal{M}}$)* | [`Proofs.v`](meta-theory/LangD/Proofs.v): `progress_m`, `preservation_m` |
| **Theorem 8** | *Absence of Stuck States ($\lambda_{\mathcal{M}}$)* | [`Proofs.v`](meta-theory/LangD/Proofs.v): `soundness_m` |
| **Theorem 9** | *Monomorphization Preserves Typing* | [`Proofs.v`](meta-theory/LangD/Proofs.v): `monomorphization_preserves_typing` |
| **Theorem 10** | *Forward Semantic Simulation* | [`Proofs.v`](meta-theory/LangD/Proofs.v): `simulation_multi` |
| **Theorem 11** | *Monomorphization Existence* | [`Proofs.v`](meta-theory/LangD/Proofs.v): `mono_expr_exists` |
| **Theorem 13** | **End-to-End Soundness Theorem** | [`Proofs.v`](meta-theory/LangD/Proofs.v): `end_to_end_soundness` |

---

## Repository Structure

```text
├── paper.pdf                 # Compiled 29-page preprint (12pt, letterpaper)
├── references.bib            # Bibliography database
├── _CoqProject               # Coq compilation configuration
├── assets/                   # Figures and assets (e.g. orcid.pdf)
└── meta-theory/
    └── LangD/                # Complete formalization of the paper
        ├── Maps.v            # Contexts, total and partial maps
        ├── Definitions.v     # Syntax, typing rules, operational semantics, catalogs
        ├── Typing.v          # Source calculus metatheory and type soundness
        └── Proofs.v          # Monomorphization, simulation, and end-to-end soundness
```

---

## How to Build and Verify

### 1. Verifying the Coq Mechanization

The formalization requires **Coq / Rocq 9.1.0+** or the **Rocq Prover** with the standard library.

Using `coq_makefile`:
```bash
# Generate Makefile from _CoqProject
rocq makefile -f _CoqProject -o Makefile

# Compile and check all proofs
make
```

All lemmas and theorems in `meta-theory/LangD/` compile cleanly with **0 `Admitted`** and **0 non-standard axioms**.

### 2. Compiling the Paper

The paper is compiled with `pdflatex` and `bibtex` using TeX Live:

```bash
pdflatex paper.tex
bibtex paper
pdflatex paper.tex
pdflatex paper.tex
```

The output document is [`paper.pdf`](paper.pdf).

---

## Citation
 
To cite this work, please use the following BibTeX entry:
 
```bibtex
@article{vergne2026overloading,
  title     = {Static Overload Resolution and Monomorphization for Functional Languages},
  author    = {Vergne, Thomas},
  journal   = {Preprint},
  year      = {2026},
  doi       = {10.5281/zenodo.22917622},
  url       = {https://doi.org/10.5281/zenodo.22917622}
}
```

---

## License

- **Paper and documentation:** [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/)
- **Coq Mechanization:** MIT License
