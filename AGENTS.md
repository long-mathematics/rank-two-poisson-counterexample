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
- Repairs to the four exact verifiers or their reference outputs must be explicit
  and separately reviewed.
- Computational identity checks are not full manuscript or Lean certification.

## Lean formalization

- Read `FORMALIZATION_STATUS.md` and `MANUSCRIPT_MAP.md`; coverage is partial.
- Preserve existing mathematical declarations and toolchain pins. Verify before
  upgrades; never modify a separate original source directory.
- Use a root Lake project and `RankTwoPoisson/` mathematical modules.
- Place auxiliary Lean audits under `scripts/`; import every mathematical module
  through the library's build targets.
- Never introduce `sorry`, `admit`, custom axioms, or hypotheses that assume
  the conclusion. Audit transitive dependencies, not just source keywords.
- Run `lake build`, `python3 scripts/audit_sources.py`, and
  `lake env lean scripts/AxiomAudit.lean`. The audit permits only `propext`,
  `Classical.choice`, and `Quot.sound`, across all project-module declarations.
- Run `lake env lean scripts/StatementAudit.lean` when reviewing correspondence.
- Distinguish proved, partial, unverified, and missing obligations in the ledger.
  Preserve exact hypotheses and record dependencies and justified alternate routes.
- Extend coverage in focused PRs. Cover all named results
  and substantive support claims, including exact fibers, symplectic/Jacobian
  consequences, higher ranks, and an actual Weyl-algebra endomorphism with proved
  non-surjectivity. Computational checks are not Lean proofs.
- If an obligation is blocked, record the exact missing lemma/infrastructure and
  investigated approaches, then continue independent tractable obligations.
- No full-paper completion claim before final statement and transitive-axiom audits.

## Git workflow

Use a feature branch, pull request, successful applicable CI, and squash merge.
Never bypass protections, force-push main, or delete source material before
the destination is accepted. Record checks actually run and any blockers.

## Documentation

Keep this tree a current paper-and-Lean companion, not a development archive.
README covers the abstract, paper links, current coverage, reproducible checks,
citation and license. The ledger records current statements, dependencies,
remaining obligations and verification results. Do not add local source paths,
migration narratives, old drafts, redundant historical documents or obsolete
build logs. Preserve unique proof material, current certificates, dependency pins,
required notices and Git history.
