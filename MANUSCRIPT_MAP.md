# Manuscript-to-Lean map

The current mathematical source is
[`rank_two_poisson_counterexample.tex`](rank_two_poisson_counterexample.tex).
The exact claim/hypothesis/dependency/status ledger is
[`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md).

| Current module | Manuscript correspondence |
| --- | --- |
| `RankTwoPoisson/Definitions.lean` | Construction equations a–D, canonical bracket, substitution and point map |
| `RankTwoPoisson/SourceCoordinates.lean` | Polynomial source inverse: both coordinate composites and 2×2 block determinant |
| `RankTwoPoisson/Core.lean` | Three residual wedge coefficients, expanded 3×3 Jacobian determinant, three core point evaluations |
| `RankTwoPoisson/Poisson.lean` | R factorization, six brackets, two polynomial inductions for global preservation |
| `RankTwoPoisson/Collision.lean` | Three rational point evaluations and algebra-map nonautomorphism via collision |
| `RankTwoPoisson/Complex.lean` | Coefficient extension, all-polynomial complex preservation, collision, algebra-map nonautomorphism |
| `RankTwoPoisson/CharacteristicZero.lean` | Same extension for every field K of characteristic zero, without further hypotheses |

The umbrella imports `CharacteristicZero` and `Complex`; both import `Collision`,
which imports `Poisson`, which imports all remaining modules. This transitive
closure is checked by `scripts/audit_sources.py`, and the root Lake library is
the default build target. Auxiliary Lean audits live under `scripts/` and run
explicitly after the library build.

The nonautomorphism argument substitutes an evaluation/collision proof for the
paper's irreducibility and CRT proof. An algebra equivalence would induce an
injective point map, contradicting the first two displayed source points. This
proves nonautomorphism of the actual substitution algebra homomorphism, not
merely noninjectivity of its point map, and it assumes no missing inverse facts.

The coefficient certificate records the construction's finite two-form
calculation. The global Poisson theorem independently checks the output brackets
and uses the biderivation laws; it does not depend on an unproved symplectic
criterion. The four-dimensional determinant, full form identity, complete fiber,
higher ranks and Weyl appendix are distinct obligations in the ledger.
