# Formalization status

## Current repository status

**Local Lean development not yet imported or reverified.**

This migration contains the manuscript, its existing PDF, four exact Python
verification programs, their historical output files, and non-Lean CI.
There are no Lean declarations or Lake configuration files in this stage.
Successful paper/identity CI is not evidence of Lean coverage.

The owner reports an existing local formalization. Earlier development records
refer to the `RankTwoPoisson` namespace and Lean/mathlib v4.32.1, with rational
and complex counterexample theorems. Those records are historical context, not
fresh build evidence. The supplied local project will determine the actual
toolchain, source inventory, and current proof status.

## Import and acceptance checklist

- Obtain the complete local project, including all Lean sources, Lake config,
  `lake-manifest.json`, `lean-toolchain`, manuscript map, and audit documents.
  Exclude `.lake/`, compiled objects, and other build caches.
- Record provenance and first build the unchanged project with its existing pins.
- Keep Lake configuration and the umbrella module at repository root;
  mathematical modules belong in `RankTwoPoisson/`.
- Preserve theorem names and proof content. Move only auxiliary audit/certificate
  tools and their recorded outputs into `scripts/`, updating references.
- Build every project module from a clean checkout using pinned Lean and mathlib.
- Audit project sources for `sorry`, `admit`, added axioms, unchecked shortcuts,
  and proof modules omitted from the build.
- Audit transitive axiom dependencies. The permitted foundations are
  `propext`, `Classical.choice`, and `Quot.sound`; report anything else.
- Map each manuscript result to actual declarations and explicit hypotheses.
  Check preservation of the bracket on all polynomials, not only generators,
  and distinguish nonautomorphism, noninjectivity of the point map, and exact
  fiber classification.
- Audit rational, complex, and general characteristic-zero statements separately.
  Also inventory the symplectic/Jacobian consequences, higher-rank extension,
  and Weyl-algebra appendix; do not infer their coverage from the main theorem.
- Add `.github/workflows/lean-ci.yml` with the job name
  `Build and audit Lean`, running the real build and source/axiom audits.
- Require successful CI before squash merge and configure the agreed main ruleset.

Until these checks are complete, no full-paper Lean certification is claimed.

## Migration validation

The manuscript compiles to 17 pages without LaTeX warnings. Exact script results
and the migration commit are recorded in the migration pull request.
The original TeX, PDF, and four verifier/output pairs are preserved byte-for-byte
under their new paths.
