# An Explicit Counterexample to the Rank-Two Poisson Conjecture

Christopher D. Long

[arXiv:2608.23777](https://arxiv.org/abs/2608.23777) · [Paper PDF](rank_two_poisson_counterexample.pdf) · [LaTeX source](rank_two_poisson_counterexample.tex) · [Formalization status](FORMALIZATION_STATUS.md)

[![Build paper and verify identities](https://github.com/long-mathematics/rank-two-poisson-counterexample/actions/workflows/verification.yml/badge.svg)](https://github.com/long-mathematics/rank-two-poisson-counterexample/actions/workflows/verification.yml)

[![Build and audit Lean](https://github.com/long-mathematics/rank-two-poisson-counterexample/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/long-mathematics/rank-two-poisson-counterexample/actions/workflows/lean-ci.yml)

This companion repository contains the manuscript, exact computational checks,
and the Lean formalization of the main counterexample over ℚ, ℂ, and
arbitrary characteristic-zero fields. **Full-paper coverage is still in progress.**
The determinant/symplectic consequences, exhaustive fiber, higher-rank extension,
and Weyl appendix are separate obligations in the
[coverage ledger](FORMALIZATION_STATUS.md).

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
| `RankTwoPoisson.lean`, `RankTwoPoisson/` | Root umbrella and mathematical Lean modules |
| `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` | Pinned root Lake project |
| `scripts/` | Exact verifiers, source/axiom audits, and current checked outputs |
| `FORMALIZATION_STATUS.md` | Named results, supporting obligations, exact coverage and dependencies |
| `MANUSCRIPT_MAP.md` | Module correspondence and alternate proof routes |
| `CITATION.cff` | Citation metadata and arXiv DOI |
| `AGENTS.md` | Mathematical integrity and repository instructions |

## Build the paper

With TeX Live and latexmk installed:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error rank_two_poisson_counterexample.tex
```

The PDF is intentionally tracked; LaTeX auxiliary files are ignored.

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

With elan installed, reproduce the pinned build and audits:

```sh
lake exe cache get
lake build
python3 scripts/audit_sources.py
lake env lean scripts/AxiomAudit.lean
lake env lean scripts/StatementAudit.lean
```

Lean is pinned to `leanprover/lean4:v4.32.1`; mathlib is `v4.32.1` at
`520045ab14e26149ee970e2e617ca04b09bde5d6`. The manifest fixes all transitive
revisions. Do not run `lake update` merely to rebuild. The library imports all of
Mathlib, so the first cache download is substantial.
For a clean project rebuild retaining only dependency caches:

```sh
lake clean rank_two_poisson
lake build
```

The exported statements are `RankTwoPoisson.explicit_counterexample`,
`RankTwoPoisson.explicit_counterexample_complex`, and
`RankTwoPoisson.explicit_counterexample_charZero K` (only `[Field K] [CharZero K]`).
They prove bracket preservation for every pair of polynomials and nonautomorphism
of the substitution algebra map. The proof uses an explicit point collision;
it does not claim that the entire three-point fiber has been classified in Lean.

[Lean CI](.github/workflows/lean-ci.yml) builds all seven mathematical modules
through the default root library. It checks source escapes, import closure,
the named-result ledger, and transitive axiom dependencies of every declaration
originating in a project module, including private/generated constants. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted.
Current verification results are recorded in the [coverage ledger](FORMALIZATION_STATUS.md).
Paper and exact-check CI remain independent.

The [original GitHub directory](https://github.com/octonion/mathematics/tree/main/poisson)
links here; the paper is [arXiv:2608.23777](https://arxiv.org/abs/2608.23777).

## Citation and license

Cite the paper using [arXiv:2608.23777](https://arxiv.org/abs/2608.23777)
or [doi:10.48550/arXiv.2608.23777](https://doi.org/10.48550/arXiv.2608.23777).
See [CITATION.cff](CITATION.cff). This repository is distributed under the
[MIT License](LICENSE). The source repository's copyright notice is retained in
[NOTICE](NOTICE).
