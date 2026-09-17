#!/usr/bin/env python3
"""Source, build-closure and named-result ledger guards; not a kernel audit.

Adapted from the source/coverage guards in entropy-constrained-missing-mass
and mathieu-property-compact-connected-lie-groups. The transitive audit is
scripts/AxiomAudit.lean; correspondence still requires mathematical review.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "RankTwoPoisson"
FORBIDDEN = re.compile(
    r"\b(sorry|admit|sorryAx|axiom|unsafe|native_decide|implemented_by|extern|"
    r"ofReduceBool|ofReduceNat|trustCompiler|skipKernelTC)\b|\bby\?")
META = re.compile(r"\b(run_cmd|run_tac|elab|macro|syntax|initialize)\b")


def code_only(source: str) -> str:
    """Blank nested comments and ordinary strings, preserving line positions.

    Interpolated strings retain their contents conservatively so executable
    expressions cannot hide escapes. This is a guard, not a full Lean parser.
    """
    out = list(source)
    i = 0

    def blank(start, end):
        out[start:end] = ["\n" if c == "\n" else " " for c in source[start:end]]

    while i < len(source):
        if source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            blank(i, end)
            i = end
        elif source.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unterminated block comment")
            blank(start, i)
        elif source[i] == '"':
            start = i
            interpolated = i > 0 and source[i - 1] == "!"
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            if i >= len(source):
                raise ValueError("Unterminated string")
            i += 1
            if not interpolated:
                blank(start, i)
        else:
            i += 1
    return "".join(out)


def check_sources(root: Path) -> tuple[int, int]:
    files = sorted(p for p in root.rglob("*.lean")
                   if not {".lake", ".git", ".venv"}.intersection(p.relative_to(root).parts))
    modules = {}
    for path in files:
        rel = path.relative_to(root)
        body = code_only(path.read_text())
        bad = FORBIDDEN.search(body)
        if bad:
            line = body.count("\n", 0, bad.start()) + 1
            raise ValueError(f"{rel}:{line}: forbidden proof escape {bad[0]}")
        if rel.parts[0] == PROJECT or rel == Path(PROJECT + ".lean"):
            if META.search(body):
                raise ValueError(f"{rel}: metaprogramming belongs in audited auxiliary tools")
            modules[".".join(rel.with_suffix("").parts)] = body
        elif rel != Path("lakefile.lean") and rel.parts[0] != "scripts":
            raise ValueError(f"{rel}: mathematical sources must be under {PROJECT}/")
    config = code_only((root / "lakefile.lean").read_text())
    if not re.search(r"@\[default_target\]\s*lean_lib\s+RankTwoPoisson\s+where\s*$", config):
        raise ValueError("Expected the root RankTwoPoisson library as default Lake target")
    visited = set()

    def visit(module):
        if module in visited:
            return
        if module not in modules:
            raise ValueError(f"Missing project module: {module}")
        visited.add(module)
        for line in re.findall(r"^\s*import\s+([^\n]+)", modules[module], re.M):
            for dependency in line.split():
                if dependency == PROJECT or dependency.startswith(PROJECT + "."):
                    visit(dependency)

    visit(PROJECT)
    if missing := modules.keys() - visited:
        raise ValueError(f"Modules absent from build umbrella: {sorted(missing)}")
    return len(files), len(visited)


def check_ledger(root: Path) -> int:
    manuscript = (root / "rank_two_poisson_counterexample.tex").read_text()
    labels = []
    for kind, body in re.findall(
            r"\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}",
            manuscript, re.S):
        label = re.search(r"\\label\{([^}]+)\}", body)
        if not label:
            raise ValueError(f"Unlabelled manuscript {kind}")
        labels.append(label[1])
    ledger = (root / "FORMALIZATION_STATUS.md").read_text()
    entries = re.findall(r"^\| `((?:thm|lem|prop|cor):[^`]+)` \| (PROVED|PARTIAL|MISSING|UNVERIFIED) \|", ledger, re.M)
    names = [name for name, _ in entries]
    if set(names) != set(labels) or len(names) != len(set(names)) or len(labels) != len(set(labels)):
        raise ValueError("Named manuscript results and status ledger differ")
    rows = re.findall(r"^\| ([A-Z][0-9]{2}) \| (?:PROVED|PARTIAL|MISSING|UNVERIFIED) \| .*? \| ([^\n]+) \|$", ledger, re.M)
    graph = {}
    for name, dependencies in rows:
        if name in graph:
            raise ValueError(f"Duplicate supporting obligation: {name}")
        refs = set(re.findall(r"\b[A-Z][0-9]{2}\b", dependencies))
        for prefix, first, last in re.findall(r"\b([A-Z])([0-9]{2})–\1([0-9]{2})\b", dependencies):
            refs.update(f"{prefix}{n:02d}" for n in range(int(first), int(last) + 1))
        graph[name] = refs
    done, active = set(), set()

    def visit(name):
        if name in active:
            raise ValueError(f"Circular ledger dependency: {name}")
        if name not in graph:
            raise ValueError(f"Unknown ledger dependency: {name}")
        if name in done:
            return
        active.add(name)
        for dependency in graph[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)

    for name in graph:
        visit(name)
    return len(labels)


if __name__ == "__main__":
    files, modules = check_sources(ROOT)
    results = check_ledger(ROOT)
    print(f"Source audit passed: {files} Lean files; {modules} modules in default build closure; no proof escapes.")
    print(f"Ledger inventory passed: all {results} named manuscript results have explicit statuses.")
