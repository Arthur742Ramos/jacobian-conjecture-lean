# Lean formalization of the Jacobian conjecture counterexample

[![CI](https://github.com/Arthur742Ramos/jacobian-conjecture-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/Arthur742Ramos/jacobian-conjecture-lean/actions/workflows/ci.yml)

This repository independently formalizes the explicit three-dimensional
polynomial map announced by Levent Alpöge in July 2026, together with the
constant-Jacobian calculation and an explicit nontrivial fibre. It proves the
usual dimension-three consequence over the complex numbers:

```lean
theorem JacobianCounterexample.not_jacobian_conjecture_complex :
    ¬ ∀ P : Fin 3 → MvPolynomial (Fin 3) ℂ,
      IsUnit (MvPolynomial.jacobianDet P) →
        Injective (MvPolynomial.evalMap P)
```

The map has formal Jacobian determinant `-2` and sends
`(0, 0, -1/4)`, `(1, -3/2, 13/2)`, and `(-1, 3/2, 13/2)` to
`(-1/4, 0, 0)`. The project does not make a claim about the still-open
two-dimensional Jacobian conjecture.

## Repository map

- `Challenge.lean` is the small statement surface a reader audits.
- `Solution.lean` connects the same declarations to the completed proof.
- `JacobianConjecture/` contains the definitions and proof development.
- `comparator.json` tells Comparator which declarations must match.
- `formalization.yaml` records provenance, authorship, automation, fidelity,
  and review information.
- `LICENSE` contains the Apache License 2.0 terms declared by the metadata.
- `docbuild/` is the pinned doc-gen4 project.
- `scripts/verify-comparator.sh` runs pinned Comparator, lean4export, NanoDa,
  and Landrun revisions using the checked-in configuration.

## Verification

The project uses Lean 4 v4.33.0 and a pinned Mathlib manifest:

```text
lake exe cache get
lake build
(cd docbuild && lake build JacobianConjecture:docs)
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

`Challenge.lean` contains deliberate `sorry` placeholders by design; the
proved declarations are in `JacobianConjecture/Proof.lean` and are imported by
`Solution.lean`. The final proof uses exact rational arithmetic and Mathlib's
formal polynomial differentiation, not an external computer-algebra
certificate.

## Sources and attribution

The public source announcement is:

<https://x.com/__alpoge__/status/2079028340955197566>

A related independent Lean formalization is pinned at:

<https://github.com/deancureton/jacobian/tree/0d4a9212d874226ad81ce5a926becddfa94e6a88>

The project is prepared for the [Palomar Registry](https://palomar-registry.org/).
To submit it, use the [Palomar submission form](https://submit.palomar-registry.org/).
Palomar submissions require a public repository, a fixed commit, and explicit
maintainer authorization.
