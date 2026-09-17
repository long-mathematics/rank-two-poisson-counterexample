# Formalization coverage and continuation ledger

The mathematical source of truth is `rank_two_poisson_counterexample.tex`.
The Lean library uses the `RankTwoPoisson` namespace and Lean/mathlib 4.32.1.
**This is partial paper coverage; complete coverage is the goal.**
No missing conclusion may be assumed to complete another row.

## Status and conventions

- **PROVED**: the stated Lean result passed a fresh build and axiom audit.
- **PARTIAL**: only the explicitly described components are proved.
- **MISSING**: no corresponding proof exists in the current library.
- **UNVERIFIED**: source exists but fresh verification has not yet completed.
- `Q` means `MvPolynomial (Fin 4) ℚ`, in coordinate order `(x,q,p,z)`;
  `C` means the same polynomial ring over `ℂ`;
  `K` means any universe-polymorphic field with `[Field K] [CharZero K]`.
- All declaration names below are relative to `RankTwoPoisson`.
  `Core` uses `MvPolynomial (Fin 3) ℚ` with order `(x,y,β)`.
- `IsPoisson`, `IsPoissonC`, and `IsPoissonK` quantify over **all** pairs of
  polynomials. `IsAlgAutomorphism` and its scalar extensions mean existence of
  an `AlgEquiv` with the specified underlying algebra homomorphism.
- A claim proved over Q is not automatically marked proved over C. Where no
  scalar-transport wrapper exists, that missing correspondence is stated.

## Named manuscript results

Each row includes all conclusions of the named result, including those not in
its current Lean counterpart. The source audit checks this inventory against
all named theorem/lemma/proposition/corollary environments in the manuscript.

| Manuscript label | Status | Exact scope, declarations, hypotheses, and dependencies |
| --- | --- | --- |
| `thm:main` | PROVED | `Symplectic.main_complex` bundles global bracket preservation, algebra-map nonautomorphism, the actual four-dimensional Jacobian determinant one, the exhaustive fiber iff for every complex point, and pairwise distinctness of its three points. It has no mathematical hypotheses. Dependencies P01–P03, B01–B03, F01–F09, J01. The original rational and arbitrary-characteristic-zero counterexamples are preserved. |
| `lem:symplectic-criterion` | PROVED | For arbitrary F : Fin 4 → PC, `Symplectic.criterion_complex` equates IsPoissonC (aeval F) with Jᵀ Ω J = Ω; `six_criterion_complex` equates it with the six displayed brackets; `det_of_poisson_complex` gives det J = 1. `form_entry` proves that this matrix equation is exactly the pullback two-form coefficient identity. No relations on F are assumed in either iff. Dependencies J03–J04. |
| `lem:R-factorization` | PROVED | `R_factorization : R = x * (2 - 3*x*q)` over Q, with no hypotheses. `Induced.R_factorization_charZero K` proves the actual coefficient-extended identity over every K, hence C. Exact definitions D01. |
| `prop:source-automorphism` | PROVED | `SourceCoordinates.sourceEquivK K` and `correctedEquivK K` are actual polynomial algebra equivalences over every K, hence C; `sourceEquivK_X`/`correctedEquivK_X` identify their forward coordinates, and both `*_symm_X` theorems identify their explicit inverses (the corrected inverse substitutes the fourth coordinate minus the independent core H). `source_det_charZero` and `corrected_det_charZero` prove the actual 4×4 determinants −1. S01–S05. |
| `prop:coefficient-identity` | PROVED | `Core.coefficient_identity_matrix` proves every coefficient of dr∧dh+dt∧ds equals Θ, represented by `Core.residualForm` in basis (dx,dy,dβ), over Q. It uses the original `Core.coefficient_identity` and proved wedge alternation. This is a coordinate representation of the full form equality, not an assumed differential-form law. D02, A02. |
| `thm:poisson-identities` | PROVED | `six_brackets`, `Phi_isPoisson`, and scalar-extension counterparts prove the six identities and all-polynomial preservation. `Symplectic.output_det_rational`, `output_det_complex`, and `output_det K` prove the actual 4×4 determinant consequence over Q/C/K. Dependencies D01, P01–P03, B01, J01. |
| `prop:core-jacobian` | PROVED | `Core.core_det_rational` identifies the original `Core.core_jacobian` certificate with Matrix.det of rows (r,t,s), columns (x,y,β). `Core.core_det_charZero K` transports the determinant identity to every characteristic-zero field, including C. No extra hypotheses. D02, J05. |
| `prop:induced-bracket` | PROVED | `Induced.source_bracket_determinant K f g` proves the ambient bracket of the two core-substituted polynomials equals the substitution of −det ∂(r3,f,g)/∂(x,y,β), for all independent core polynomials over K, hence C. `r3_map` and D03 identify r3 with R; S04 establishes the subalgebra coordinates are independent. `source_generators` proves all nine generator entries and `source_casimir` the Casimir property. The particular S,T consequences are P01/B01. I01–I03. |
| `prop:not-automorphism` | PROVED | `Phi_not_automorphism`, `PhiC_not_automorphism`, `PhiK_not_automorphism K` prove algebra-map nonautomorphism using explicit collisions and evaluation of an inverse algebra equivalence (F01–F05, B02–B03). This substitutes for the paper's prime-ideal/CRT argument. |
| `prop:exact-fiber` | PROVED | `Fiber.exact_fiber_complex`: for every v : Fin 4 → ℂ, pointMapC PhiC v = targetC iff v = point0C ∨ v = point1C ∨ v = complexPoint point2. `Fiber.exact_fiber_charZero` proves the same over K; `Fiber.exact_fiber_rational` covers Q. `Fiber.fiber_points_distinct` proves all three points differ. Dependencies F06–F09, S03, B02; the separate Gröbner/scheme certificate F10 is not needed. |
| `cor:all-poisson-ranks` | MISSING | For every n ≥ 2, construct a bracket-preserving nonautomorphic endomorphism on 2n polynomial variables over C. Needs N01–N03; no rank restriction may be assumed away. |
| `thm:explicit-DC4` | MISSING | Actual C-algebra endomorphism of the fourth Weyl algebra, Xi ↦ (R,T,D,S)i, ∂i ↦ (HD,HS,−HR,−HT)i, with proved defining relations and non-surjectivity. Needs W01–W09. Polynomial identities alone do not prove this result. |

## Supporting obligations and dependency order

Rows are proof obligations, not assertions that every intermediate calculation
must use the manuscript's exact proof route. An equivalent route must document
which intermediate obligations it replaces. Historical/bibliographic assertions
and reported software timings are outside mathematical formalization.

| ID | Status | Precise claim / current declaration | Dependencies |
| --- | --- | --- | --- |
| D01 | PROVED | Exact Q definitions `a,B,beta,y,u,R,S,T,D0,H,D,bracket,output,Phi` match construction equations; bracket is fp gx − fx gp + fz gq − fq gz; output order (R,T,D,S). | — |
| D02 | PROVED | `Core.r,s,t,h,Q3,A1,A2,A3,wedgeCoeff,jac3` match independent-variable construction and determinant expansion over Q. | D01 (correspondence) |
| D03 | PROVED | `SourceCoordinates.core_substitution` identifies the core substitution algebra homomorphism on r,t,s,h with R,T,S,H over Q; `core_substitution_charZero` proves all four polynomial equalities after coefficient extension to K. `Fiber.eval_r`, `eval_s`, `eval_t`, `eval_h` give the scalar evaluation versions. | D01, D02 |
| D04 | MISSING | Reported expanded term counts and total degrees of β,y,R,S,T,H,D as kernel-checked polynomial facts. | D01 |
| D05 | MISSING | Announced map (Π,Σ,ℛ): normalization G=(ℛ,−Π/2,Σ), actual Jacobian determinant −2, and common image (−1/4,0,0) of the displayed three points. | D02, J05, F08 |
| D06 | MISSING | Introductory cotangent lift of the announced map: polynomial inverse-transpose Jacobian, canonical one-form preservation, zero-section collision, and resulting counterexample on three canonical pairs. This is a separate construction from the higher-rank identity extension N02. | D05 |
| S01 | PROVED | `SourceCoordinates.source_block_det`: 2×2 block determinant equals −1, as a Q polynomial identity. | D01 |
| S02 | PROVED | `SourceCoordinates.inverse_certificate`: βBack=p, yBack=q, D0Back=z in independent inverse coordinates. | D01 |
| S03 | PROVED | `SourceCoordinates.two_sided_inverse_certificate`: S02 and Qorig=q, pRecovered=p, zRecovered=z. x is unchanged. | S02 |
| S04 | PROVED | `SourceCoordinates.sourceEquivK` and `correctedEquivK` bundle Ψ₀ and Ψ as algebra equivalences over K; `*_X` identify the forward images and `*_symm_X` the explicit inverse images, including D−H. `source_algebraicIndependent` proves algebraic independence of x,y,β over K by restricting the transported independent polynomial generators. | S03, D03 |
| S05 | PROVED | `source_det_rational`, `corrected_det_rational`, `source_det_charZero`, `corrected_det_charZero` prove full Matrix.det Jacobians equal −1 in order (x,q,p,z). The shear algebra equivalence `shearEquiv` has explicit inverse; determinant proofs directly differentiate the actual maps, replacing the manuscript’s triangular determinant argument. | S04 |
| A01 | PROVED | `Core.DerivativeCertificate.r_derivatives`, `s_derivatives`, `t_derivatives`, `h_derivatives` give all twelve first partials over Q in order (x,y,β). `P1_derivative`, `P2_derivative`, and the four evaluation lemmas identify P₁,P₂ and their derivatives exactly with the auxiliary appendix expressions. | D02 |
| A02 | PROVED | `Core.coefficient_identity` proves the three independent wedge coefficients; `Core.coefficient_identity_matrix` proves all nine entries against `residualForm`, using wedge skew symmetry and zero diagonal. The private coefficient proofs are included transitively. | D02 |
| A03 | PROVED | `Core.DerivativeCertificate.expanded_coefficients` states and proves all three displayed collected expressions, identifying them with A₁,A₂,A₃ through the original coefficient certificate. | A01, A02 |
| A04 | PROVED | `SourceCoordinates.Forms.dQ`, `dC`, `dM`, `dp`, `dz`, `dR`, `d_p_first`, `d_p_second` prove every one-form coefficient of the source calculation over Q. `omega_Q_coefficient`, `omega_Q`, and `omega_split` give the intermediate coefficient and complete alternating two-form arrays. `omega_split_charZero K` proves the actual differentiated form equality over K, hence C. The independent order is (X,Y,W,E₀); Θ is padded by a zero fourth row/column. | S04, D03 |
| P01 | PROVED | Six exact Q brackets: `bracket_D_R`, `bracket_S_T` = 1 and `bracket_R_S`, `bracket_R_T`, `bracket_D_S`, `bracket_D_T` = 0; bundled `six_brackets`. No assumed identities. | D01 |
| P02 | PROVED | `bracket_skew`, `bracket_self`, constant/additive/Leibniz laws; `bracket_X_X`, `bracket_output_output`. | D01, P01 |
| P03 | PROVED | `Phi_generator_bracket`, `Phi_preserves_right_generator`, `Phi_isPoisson`: two polynomial inductions establish ∀f g, {Φf,Φg}=Φ{f,g}. | P02 |
| P04 | PROVED | `Calculus.pderiv_comm` proves mixed-partial commutation over any commutative ring. `jacobi` and `hamiltonian_identity` prove the canonical bracket laws over every field. `hamiltonian` is an actual Derivation, and `hamiltonian_commutator` proves [Hf,Hg]=H{f,g} as an equality of derivations. No characteristic-zero assumption is needed for these laws. | D01, P02 |
| B01 | PROVED | `polyDeriv_mapC`, `bracket_mapC`, `PhiC_isPoisson`; `polyDeriv_mapK`, `bracket_mapK`, `PhiK_isPoisson K`. Derivatives/brackets commute with Q coefficient extension; all-polynomial preservation is proved afresh by induction. | P01–P03 |
| F01 | PROVED | `point0_image`, `point1_image`, `point2_image`: the three exact rational source points map to `target`. | D01 |
| F02 | PROVED | `point0_ne_point1`: first two rational points differ; `Fiber.fiber_points_distinct` proves all three pairwise distinctions over K. | F01 (definitions only) |
| F03 | PROVED | `pointMap_of_equiv_injective`: any Q-polynomial algebra equivalence induces an injective point map; no assumption that the specific Φ is invertible. | D01 |
| F04 | PROVED | `Phi_not_automorphism`, `explicit_counterexample`: contradiction between F01/F02 and F03. This is stronger than merely reporting a point collision. | F01–F03, P03 |
| F05 | PROVED | `Fiber.pointMap_not_injective` (K), `rational_pointMap_not_injective` (Q), `complex_pointMap_not_injective` (C) prove point-map noninjectivity. No noninjectivity of the algebra map is claimed. | F01, F02, B02 |
| B02 | PROVED | `aeval_mapC_complexPoint`, `pointMapC_PhiC_complexPoint`, `point0C_image`, `point1C_image`, `point0C_ne_point1C`; respective K transport theorems and points. K assumes only Field and CharZero. | F01, F02, B01 |
| B03 | PROVED | `pointMapC_of_equiv_injective`, `PhiC_not_automorphism`, `explicit_counterexample_complex`; corresponding K theorems culminating in `explicit_counterexample_charZero K`. | F03, B02, B01 |
| F06 | PROVED | `Fiber.core_fiber`: for all x,y,β over K, (rValue,tValue,sValue)=(0,1/8,0) iff (x,y,β) is (0,0,−1/4), (1,−3/2,13/2), or (−1,3/2,13/2). No assumptions beyond Field/CharZero. | D03 |
| F07 | PROVED | `Fiber.localized_core` proves the three displayed localized formulas at x≠0. `Fiber.core_fiber` separately handles x=0; polynomial combinations give xy=−3/2, x²β=13/2 and x²=1 in the nonzero case. This avoids localization infrastructure while proving the same equations. | D03 |
| F08 | PROVED | `Core.corePoint0_image`, `corePoint1_image`, `corePoint2_image`: three rational core memberships, no exhaustiveness. | D02 |
| F09 | PROVED | `Fiber.hValue_points` proves H=−1/48,−1097/192,−1097/192 on the core fiber. `recover_q`, `recover_p`, `recover_z`, `source_injective` transfer the original inverse certificates to K; `exact_fiber_charZero`, `exact_fiber_complex`, `exact_fiber_rational` exhaust the actual four-dimensional fiber. All three distinctness statements are `fiber_points_distinct`. | F06, S03, D03, B02 |
| F10 | MISSING | Gröbner certificate: equality of the fiber ideal with (β−(27x²−1)/4, y+3x/2, x(x−1)(x+1)); reduced fiber scheme. | F06 or explicit ideal identities |
| I01 | PROVED | `Induced.generators_rational` proves {x,y}=x³, {x,β}=−3x², {y,β}=−2+6xy+3x²β. `source_generators K` transports these to all nine generator entries over K. `ambient_support` exports βp, βz and {q,β} from the manuscript derivation. | D01 |
| I02 | PROVED | `Induced.source_bracket` uses two polynomial inductions to identify the ambient bracket on the entire source subalgebra. `determinant_formula` identifies it with the negative 3×3 Jacobian; `source_bracket_determinant` combines the two for all f,g over K. `casimir`, `r3_map`, and `source_casimir` prove that the actual R is a Casimir. | I01, S04, P02 |
| I03 | PROVED | `Induced.D0_R_rational`, `D0_R_charZero` prove {D₀,R}=1 over Q/K; `H_R_charZero` proves {H,R}=0 over K, hence C, using the full subalgebra Casimir result and the proved core-H substitution. | I02, D01 |
| J01 | PROVED | `Symplectic.output_det K`, `output_det_complex`, `output_det_rational`: Matrix.det of the actual formal Jacobian with rows (R,T,D,S), columns (x,q,p,z), equals 1. `jacobian` and `jacobian_pair` fix the coordinate and bracket conventions. | P01, B01, J03 |
| J02 | PROVED | `Symplectic.output_symplectic K`, `output_symplectic_complex` prove Jᵀ Ω J=Ω. `output_form_coefficients` spells out every coefficient of dR∧dD+dT∧dS = dx∧dp+dq∧dz, with Ω explicitly defined by `omega`. | P01, B01, J03 |
| J03 | PROVED | `Symplectic.conjugate_iff` proves the equivalence of primal/dual form identities for inverse matrices U,V; `omega_mul_neg` and `neg_mul_omega` prove the actual inverse identities Ω⁻¹=−Ω. `det_pair` proves the signed 4×4 contraction formula over any commutative ring, giving determinant +1. | — |
| J04 | PROVED | `Symplectic.preserves_of_generators` proves all-polynomial preservation for any algebra homomorphism from its generator identities. `poisson_iff_canonical`, `canonical_iff_six`, `poisson_iff_symplectic`, and their explicit complex wrappers assemble the general criterion. | P02, J03 |
| J05 | PROVED | `Core.core_det_rational` identifies the actual 3×3 Matrix.det with the original expanded `jac3` certificate. `core_det_charZero K` commutes coefficient mapping with partial differentiation and determinants to prove the same polynomial identity over K. | D02 |
| J06 | MISSING | Localized core source/target determinant factors and point-map factorization σ∘(G×id)∘Ψ. May be replaced by direct determinant proof, with correspondence documented. | S04, J05, D03 |
| N01 | MISSING | Canonical bracket on n pairs with variable order and embedding of the four original coordinates explicit; bracket laws. | P02 (proof route) |
| N02 | MISSING | For every n≥2 extend Φ by identity on remaining pairs and prove global bracket preservation. | N01, P03, B01 |
| N03 | MISSING | Extend the displayed collision to n pairs and prove nonautomorphism of the algebra map. This can replace the paper's irreducibility argument. | N02, B02, F03 |
| W01 | MISSING | Actual fourth Weyl algebra over C with generators Xi,∂i and the stated universal defining relations; polynomial representation. | noncommutative algebra infrastructure |
| W02 | MISSING | Hamiltonian derivations HD,HS,−HR,−HT as elements of that algebra; δi(fj)=δij. | W01, B01 |
| W03 | MISSING | [HF,HG]=H{F,G} and commutation of δi; multiplication operators fi commute. | P04, W01, W02 |
| W04 | MISSING | Construct actual endomorphism widehatΦ using the universal property and all Weyl relations; verify generator images. | W02, W03 |
| W05 | MISSING | Polynomial substitution ΦC is injective / fi are algebraically independent, via invertible formal Jacobian or canonical derivations. | J01 or W02 |
| W06 | MISSING | Weyl PBW basis, differential-order filtration, associated graded C[X,ξ], and principal-symbol formulas. These support the manuscript route; an equivalent non-surjectivity argument may avoid them. | W01 |
| W07 | MISSING | A Jfᵀ=I and A invertible; symbol monomials η^β independent; no cancellation of highest differential order. | J01, W02, W05, W06 |
| W08 | MISSING | Prove non-surjectivity of the actual Weyl endomorphism, then nonautomorphism, without assuming either. Investigate alternative: the image operators preserve C[f] and send 1 into C[f]; surjectivity would force every multiplication polynomial into C[f], contradicting the collision. | W04, B02; manuscript route also W05–W07 |
| W09 | MISSING | Correspondence of quotient/universal Weyl construction to the manuscript differential-operator model; faithfulness/PBW if needed by the chosen route. | W01, W06 |

## Fresh validation

- Lean `4.32.1`, compiler commit `f054605aea4b840552cca2e725580bffd1e1b704`.
- mathlib `v4.32.1`, revision `520045ab14e26149ee970e2e617ca04b09bde5d6`;
  all nine dependency revisions match `lake-manifest.json`.
- `lake build`: passed, 8,671 jobs. CI rebuilds every project module from source.
  The 86 existing warnings concern unused simp arguments, tactic style and section variables;
  there are no build errors. Pinned dependency caches are reused.
- `python3 scripts/audit_sources.py`: passed for 19 Lean files and all sixteen
  library modules (fifteen mathematical files plus umbrella). All 12 named results
  have ledger entries; the 53 supporting obligations have acyclic dependencies.
- `lake env lean scripts/AxiomAudit.lean`: passed for all 533 declarations
  originating in project modules, including 399 theorem constants and all
  private/generated declarations. Every transitive axiom set is contained in
  `{propext, Classical.choice, Quot.sound}`. Current output is
  [`scripts/axiom-audit.txt`](scripts/axiom-audit.txt).
- `lake env lean scripts/StatementAudit.lean`: main statements, definitions,
  quantifiers, coordinate ordering and field hypotheses inspected successfully.
- All four exact Python verifiers passed with empty stderr and byte-for-byte
  recorded-output matches; expected outputs were not changed. All 19 regression
  tests pass (six verification-runner tests, thirteen source/coverage tests).
- The manuscript and PDF are unchanged. Paper and exact-verification CI are
  retained alongside the `Build and audit Lean` job.
- Hosted verification results are available through the README workflow badges.

## Continuation plan

1. Maintain passing builds, exact Python checks, source/module/ledger audits,
   transitive axiom audits, CI, and main-only protection.
2. Complete the separate ideal/scheme certificate F10, term counts D04, and
   announced-map/cotangent-lift claims D05–D06. Coordinate-algebra correspondence,
   exhaustive point-fiber classification, and Appendix A certificates are proved.
3. Close the remaining localized core and point-map factorization claims J06.
   The induced bracket, Casimir property, source form, four-dimensional Jacobian,
   and general symplectic criterion are proved.
4. Higher rank construction and proof.
5. Weyl presentation, Hamiltonian relations, actual endomorphism and
   non-surjectivity; assess PBW/model-correspondence requirements explicitly.
6. Close remaining substantive support claims and run a final full statement
   correspondence and transitive-axiom audit before claiming complete coverage.

No substantive mathematical error has been identified in the inspected Lean
statements. This is not a certification of the manuscript's missing results.
