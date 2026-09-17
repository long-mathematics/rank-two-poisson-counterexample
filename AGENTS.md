# Repository instructions

## Manuscript and integrity

- The canonical source is `rank_two_poisson_counterexample.tex`; its PDF is tracked.
- Preserve mathematical statements, hypotheses, proof content, authorship, notation,
  and stable labels unless explicitly instructed to change them.
- Flag suspected mathematical errors; do not silently repair or weaken claims.
- Keep mathematical changes separate from migration and editorial changes.
- Compile with `latexmk -pdf -interaction=nonstopmode -halt-on-error rank_two_poisson_counterexample.tex`.
  Check undefined citations/references and layout warnings before committing a new PDF.
- Do not commit LaTeX auxiliary files or build caches.

## Exact verification

- Auxiliary verification/audit scripts and checked outputs belong in `scripts/`.
- Install `scripts/requirements.txt`, run
  `python -m unittest discover -s scripts -p 'test_*.py'` and
  `python scripts/check_verification.py`.
- Do not silently regenerate expected outputs to make tests pass.
- The four migrated scripts and outputs are provenance-preserved. A future repair
  must be explicit and separately reviewed.
- Computational identity checks are not full manuscript or Lean certification.

## Lean import

- Read `FORMALIZATION_STATUS.md`. There are no Lean sources in the initial migration.
- Preserve the existing local formalization, namespace, declaration names and
  toolchain pins when importing. Verify before attempting upgrades.
- Use a root Lake project and `RankTwoPoisson/` mathematical modules.
- Place auxiliary Lean audits under `scripts/`; import every mathematical module
  through the library's build targets.
- Never introduce `sorry`, `admit`, custom axioms, or hypotheses that assume
  the conclusion. Audit transitive dependencies, not just source keywords.
- Distinguish proved, unverified, and missing obligations in the manuscript ledger.

## Git workflow

Use a feature branch, pull request, successful applicable CI, and squash merge.
Never bypass protections, force-push main, or delete source material before
the destination is accepted. Record checks actually run and any blockers.
