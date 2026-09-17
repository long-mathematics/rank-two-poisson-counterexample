# An Explicit Counterexample to the Rank-Two Poisson Conjecture

Christopher D. Long

[arXiv:2608.23777](https://arxiv.org/abs/2608.23777) · [Paper PDF](rank_two_poisson_counterexample.pdf) · [LaTeX source](rank_two_poisson_counterexample.tex) · [Formalization status](FORMALIZATION_STATUS.md)

[![Build paper and verify identities](https://github.com/long-mathematics/rank-two-poisson-counterexample/actions/workflows/verification.yml/badge.svg)](https://github.com/long-mathematics/rank-two-poisson-counterexample/actions/workflows/verification.yml)

This is the companion repository for the paper, with exact computational checks.
An existing local Lean development is awaiting import and fresh verification; **no
Lean sources are included in this migration**, and the CI badge does not certify Lean proofs.

## Abstract

Let

$$
\mathcal{P}_2=\mathbb{C}[x,q,p,z]
$$

carry the canonical Poisson bracket determined by

$$
\{p,x\}=\{z,q\}=1
$$

and by the vanishing of the other brackets between distinct generators. Here and throughout, “rank two” means two canonical pairs in the standard indexing of the canonical Poisson algebras; thus there are four polynomial generators and the Poisson tensor has geometric rank four. We give explicit polynomials

$$
R,T,D,S\in\mathbb{Q}[x,q,p,z]
$$

satisfying

$$
\{D,R\}=1,\qquad \{S,T\}=1,
$$

and

$$
\{R,S\}=\{R,T\}=\{D,S\}=\{D,T\}=0,
$$

while

$$
R=x(2-3xq).
$$

Consequently, the assignment

$$
(x,q,p,z)\mapsto(R,T,D,S)
$$

defines a Poisson endomorphism of $\mathcal{P}_2$ that is not an automorphism. This disproves the Poisson Conjecture for two canonical pairs, and hence for every number of canonical pairs at least two. The associated polynomial map of $\mathbb{A}^4$ preserves the canonical symplectic form, has Jacobian determinant one, and has an explicit fiber consisting of exactly three points. The proof uses a polynomial source coordinate system in which the symplectic identity reduces to three displayed coefficient identities. A separate appendix uses the same four output polynomials and their Hamiltonian duals to construct an explicit nonautomorphic endomorphism of the fourth Weyl algebra.

## Repository contents

| Path | Purpose |
| --- | --- |
| `rank_two_poisson_counterexample.tex` | Canonical manuscript source |
| `rank_two_poisson_counterexample.pdf` | Tracked paper PDF |
| `scripts/` | Four preserved verifiers, recorded outputs, and the test runner |
| `FORMALIZATION_STATUS.md` | Lean import status and verification requirements |
| `CITATION.cff` | Citation metadata and arXiv DOI |
| `AGENTS.md` | Mathematical integrity and repository instructions |

## Build the paper

With TeX Live and latexmk installed:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error rank_two_poisson_counterexample.tex
```

The PDF is intentionally tracked; LaTeX auxiliary files are ignored. The migrated
TeX and PDF are byte-for-byte copies of their source versions, renamed only.
A fresh local compilation was also checked during migration.

## Reproduce the exact checks

Python 3.12 is used in CI. The reference SymPy output records version 1.12.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r scripts/requirements.txt
python -m unittest discover -s scripts -p 'test_*.py'
python scripts/check_verification.py
```

The runner executes all four verifiers with assertions enabled and requires
successful exits, empty standard error, and byte-for-byte agreement with the
checked-in outputs. A difference is a failure, not an automatically updated baseline.

| Verifier | Recorded output |
| --- | --- |
| [SymPy bracket/determinant check](scripts/verify_rank2_poisson_counterexample.py) | [Output](scripts/verify_rank2_poisson_counterexample.txt) |
| [Independent rational sparse-polynomial check](scripts/verify_rank2_poisson_sparse.py) | [Output](scripts/verify_rank2_poisson_sparse.txt) |
| [Structural SymPy audit](scripts/verify_rank2_poisson_sympy.py) | [Output](scripts/verify_rank2_poisson_sympy.txt) |
| [Additional algebraic audit](scripts/verify_rank2_poisson_claude_audit.py) | [Output](scripts/verify_rank2_poisson_claude_audit.txt) |

These are computational checks of the identities encoded in each program, not
a claim of full manuscript formalization. The additional audit script includes
a constant-true determinant reporting line; that line is not an independent
test. The determinant is actually computed by the other verifiers.

## Lean formalization

The existing local development will be imported without restarting the proofs.
The intended layout is a root Lake project with `RankTwoPoisson.lean`,
mathematical modules under `RankTwoPoisson/`, and audit tools and outputs under
`scripts/`. Preserve existing declaration names. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the acceptance checklist.

## Provenance and workflow

The manuscript and four script/output pairs were copied from
[`octonion/mathematics/poisson` at `eef71f7b64ad`](https://github.com/octonion/mathematics/tree/eef71f7b64adfb3512a5d006db15d1e51965e8fc/poisson).
The source repository retains the historical commits. This is a snapshot migration,
not a rewritten or imported Git history. The old directory remains intact until
the destination migration is accepted.

Changes use a feature branch and pull request, then successful checks and squash
merge. After Lean CI is operational, the intended main-branch ruleset requires
`Build and audit Lean`, prohibits force pushes and deletion, and has no bypass,
human-approval requirement, signed-commit requirement, or strict freshness requirement.
That ruleset is a setup target, not a claim that it is already active.

## Citation and license

Cite the paper using [arXiv:2608.23777](https://arxiv.org/abs/2608.23777)
or [doi:10.48550/arXiv.2608.23777](https://doi.org/10.48550/arXiv.2608.23777).
See [CITATION.cff](CITATION.cff). This repository is distributed under the
[MIT License](LICENSE). The source repository's copyright notice is retained in
[NOTICE](NOTICE).
