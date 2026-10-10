#!/usr/bin/env python3
"""Source-only policy checks. Never imports, launches, or evaluates Lean.

This is a lexical guard for this draft, not a Lean parser or an axiom audit.
Only a later kernel check can establish correctness and transitive axioms.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_REV = "c55e6e786f49471c72fbddbec5415808896aec1e"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
FORBIDDEN = {
    "sorry", "admit", "axiom", "sorryAx", "native_decide",
    "native_decide_eq_true", "ofReduceBool", "ofReduceNat", "unsafe",
    "extern", "implemented_by", "run_tac", "run_elab", "elab", "elab_rules",
    "macro", "macro_rules", "initialize", "builtin_initialize", "opaque",
}
DECLARATION = re.compile(
    r"^(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|class)\s+([\w.']+)",
    re.MULTILINE,
)
IMPORT = re.compile(r"^import\s+([^\n]+)", re.MULTILINE)


def code_only(source: str) -> str:
    """Blank comments (including nested blocks) and strings, preserving lines."""
    result = list(source)
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                result[i:i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                result[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif quoted:
            if source[i] == "\\":
                for j in range(i, min(i + 2, len(source))):
                    if source[j] != "\n":
                        result[j] = " "
                i += 2
            else:
                if source[i] == '"':
                    quoted = False
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end == -1:
                end = len(source)
            result[i:end] = " " * (end - i)
            i = end
        elif source.startswith("/-", i):
            result[i:i + 2] = "  "
            depth = 1
            i += 2
        elif source[i] == '"':
            result[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError("unclosed block comment or string")
    return "".join(result)


def main() -> int:
    errors: list[str] = []
    files = sorted(
        p for p in ROOT.rglob("*.lean")
        if not {".git", ".lake"}.intersection(p.relative_to(ROOT).parts)
    )
    if not files:
        errors.append("no project Lean files found")
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in files}
    graph: dict[str, list[str]] = {}
    declarations: set[str] = set()
    theorem_count = 0
    cleaned: dict[Path, str] = {}
    for module, path in modules.items():
        source = path.read_text(encoding="utf-8")
        label = str(path.relative_to(ROOT))
        try:
            code = code_only(source)
        except ValueError as error:
            errors.append(f"{label}: {error}")
            continue
        cleaned[path] = code
        if not source.endswith("\n"):
            errors.append(f"{label}: missing final newline")
        if any(line.rstrip() != line for line in source.splitlines()):
            errors.append(f"{label}: trailing whitespace")
        identifiers = set(re.findall(r"\b[\w']+\b", code))
        prohibited = identifiers & FORBIDDEN
        if prohibited:
            errors.append(f"{label}: prohibited identifiers {sorted(prohibited)}")
        if re.search(r"#(?:eval|reduce|run|compile)\b|debug\.skipKernelTC", code):
            errors.append(f"{label}: prohibited evaluation or trust-bypass command")
        imports = [name for row in IMPORT.findall(code) for name in row.split()]
        graph[module] = [name for name in imports if name != "Mathlib"]
        for name in imports:
            if name != "Mathlib" and name not in modules:
                errors.append(f"{label}: import outside Mathlib/project: {name}")
        if module.startswith("AmbidextrousSofa."):
            if not re.search(r"^namespace AmbidextrousSofa$", code, re.MULTILINE):
                errors.append(f"{label}: expected the project namespace")
            for kind, name in DECLARATION.findall(code):
                qualified = f"AmbidextrousSofa.{name}"
                if qualified in declarations:
                    errors.append(f"duplicate named declaration: {qualified}")
                declarations.add(qualified)
                theorem_count += kind in {"theorem", "lemma"}

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visiting:
            errors.append(f"import cycle at {module}")
            return
        if module in visited:
            return
        visiting.add(module)
        for dependency in graph.get(module, []):
            visit(dependency)
        visiting.remove(module)
        visited.add(module)

    visit("AmbidextrousSofa")
    missing_modules = {m for m in modules if m.startswith("AmbidextrousSofa.")} - visited
    if missing_modules:
        errors.append(f"entry point misses modules: {sorted(missing_modules)}")
    for module in graph:
        visit(module)

    audit = cleaned.get(ROOT / "AxiomAudit.lean", "")
    queries = re.findall(r"^#print axioms ([\w.']+)\s*$", audit, re.MULTILINE)
    if set(queries) != declarations or len(queries) != len(declarations):
        errors.append("future axiom audit does not cover each named declaration exactly once")

    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        errors.append("unexpected Lean toolchain pin")
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    if config.get("leanOptions", {}).get("autoImplicit") is not False:
        errors.append("autoImplicit must remain false")
    requirements = config.get("require", [])
    if len(requirements) != 1 or requirements[0].get("name") != "mathlib":
        errors.append("expected Mathlib as the sole direct dependency")
    elif requirements[0].get("rev") != MATHLIB_REV:
        errors.append("unexpected Mathlib revision in package configuration")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {p["name"]: p for p in manifest["packages"]}
    mathlib = packages.get("mathlib", {})
    if mathlib.get("rev") != MATHLIB_REV or mathlib.get("inputRev") != MATHLIB_REV:
        errors.append("Mathlib lockfile pin differs from the exact requested revision")
    if any(not re.fullmatch(r"[0-9a-f]{40}", p.get("rev", "")) for p in packages.values()):
        errors.append("every dependency must have a full commit revision")
    if manifest.get("name") != "AmbidextrousSofa":
        errors.append("lockfile names a different root package")

    ci_paths = [
        ".github/workflows", ".circleci", ".gitlab-ci.yml", "Jenkinsfile",
        "azure-pipelines.yml", ".travis.yml",
    ]
    for relative in ci_paths:
        if (ROOT / relative).exists():
            errors.append(f"CI configuration is prohibited in this draft: {relative}")
    if errors:
        print("SOURCE POLICY FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"Source policy passed: {len(files)} Lean files; {theorem_count} named theorems;")
    print(f"{len(declarations)} named declarations covered by unexecuted axiom queries.")
    print("Imports and dependency pins checked; no CI configuration found.")
    print("No Lean execution occurred. This is not a kernel proof or axiom audit.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
