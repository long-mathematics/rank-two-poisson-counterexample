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
| `RankTwoPoisson/ExactFiber.lean` | Exhaustive three-point fiber over Q/C/K, pairwise distinctness, localized formulas, source-coordinate recovery and H-values |
| `RankTwoPoisson/Symplectic.lean` | General symplectic criterion, actual 4×4 Jacobian and form preservation, bundled main theorem |
| `RankTwoPoisson/SourceEquivalence.lean` | Actual source and corrected algebra equivalences over K, explicit inverses, core substitution, algebraic independence, and source Jacobians |
| `RankTwoPoisson/PoissonCalculus.lean` | Mixed partials, Jacobi identity, and Hamiltonian derivation commutators |
| `RankTwoPoisson/InducedBracket.lean` | All-polynomial induced negative-Jacobian bracket over K, Casimir R, and separate D₀/R and H/R identities |
| `RankTwoPoisson/DerivativeCertificate.lean` | Appendix A: all first derivatives and three expanded coefficient expressions |
| `RankTwoPoisson/SourceForms.lean` | All source differential and two-form coefficients, including ω=dR∧dD₀+Θ |
| `RankTwoPoisson/HigherRank.lean` | Identity extension, explicit canonical reindexing, and non-surjective Poisson endomorphisms for every n≥2 over K |
| `RankTwoPoisson/CoreGeometry.lean` | Actual 3×3 core Jacobian over Q/K and complete residual form coefficient matrix |

The umbrella imports every mathematical layer, including the source-equivalence and
Poisson-calculus modules. The counterexample chain runs through `CharacteristicZero` and
`Complex` to `Collision`, `Poisson`, `Core`, `SourceCoordinates`, and `Definitions`. This transitive
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
criterion. The exact fiber proof solves the core equations by polynomial combinations,
including the x=0 case, and recovers original coordinates from the proved inverse
certificates. It also exports the manuscript's localized formulas. The
four-dimensional determinant and full form identity are proved in `Symplectic`.
The matrix Ω represents dx∧dp+dq∧dz, its inverse −Ω is the bracket matrix, and
`form_entry` identifies each pulled-back coefficient with JᵀΩJ. A directly
proved 4×4 contraction formula establishes determinant +1. `CoreGeometry`
identifies the old expanded core determinant with Matrix.det and transports it
coefficientwise. The Weyl endomorphism remains open.

The source coordinate automorphisms are represented contravariantly by
substitution algebra equivalences. Their inverse generator images are the
paper’s explicit inverse formulas. The corrected equivalence composes the
uncorrected one with the independent-coordinate shear, whose inverse subtracts
H. Both full source Jacobians are differentiated directly and coefficientwise
transported to K, giving the same determinant −1 as the triangular argument.
`PoissonCalculus` supplies Jacobi and equality of Hamiltonian commutators as
actual derivations; these results alone do not construct a Weyl endomorphism.

The induced bracket is first defined explicitly as a biderivation in the three
independent variables. Two polynomial inductions identify it with the ambient
bracket on the full source-coordinate subalgebra; the negative determinant
formula is proved for arbitrary f,g, not only the three generators. The appendix
derivative certificates state the complete displayed lists, while `SourceForms`
represents one-forms by all four coefficients and two-forms by all sixteen
alternating entries, in independent order (X,Y,W,E₀).

For higher rank, the original four variables are first adjoined to m independent
canonical pairs. The substitution fixes every extra generator, and an explicit
variable equivalence sends (x,q,p,z) to ((0,0),(1,0),(0,1),(1,1)) in the first
two pairs. `reindex_bracket` proves that this carries the bracket to the
manuscript’s exact sum on 2+m pairs. The original collision extends by zeros;
surjectivity would make the point map injective. Conjugation by the variable
equivalence preserves this contradiction, giving non-surjectivity and hence
nonautomorphism for every n≥2, over C and every characteristic-zero field.
