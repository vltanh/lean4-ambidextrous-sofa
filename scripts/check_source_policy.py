#!/usr/bin/env python3
"""Source-only policy checks. Never imports, launches, or evaluates Lean.

This is a lexical guard for this draft, not a Lean parser or an axiom audit.
Only a later kernel check can establish correctness and transitive axioms.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]
MATHLIB_REV = "c55e6e786f49471c72fbddbec5415808896aec1e"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
PROJECT_NAMESPACE = "AmbidextrousSofa"
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
FORBIDDEN = {
    "sorry", "admit", "axiom", "sorryAx", "native_decide",
    "native_decide_eq_true", "ofReduceBool", "ofReduceNat", "unsafe",
    "extern", "implemented_by", "run_tac", "run_elab", "elab", "elab_rules",
    "macro", "macro_rules", "initialize", "builtin_initialize", "opaque",
}
IDENTIFIER = r"(?:[^\W\d]|_)[\w']*"
LEAN_NAME = rf"{IDENTIFIER}(?:\.{IDENTIFIER})*"
MODIFIER_WORDS = "noncomputable|protected|private|public"
MODIFIERS = rf"(?:(?:{MODIFIER_WORDS})\s+)*"
DECLARATION_KINDS = "theorem|lemma|def|abbrev|structure|class|inductive|instance"
DECLARATION = re.compile(
    rf"^(?P<modifiers>{MODIFIERS})(?P<kind>{DECLARATION_KINDS})\s+"
    rf"(?P<name>{LEAN_NAME})(?=$|[\s:({{])"
)
# Recognize unsupported declaration prefixes as well, so they are rejected
# instead of silently falling outside the inventory.
DECLARATION_START = re.compile(
    rf"^(?:(?:{MODIFIER_WORDS}|nonrec|local|scoped|partial)\s+)*"
    rf"(?:{DECLARATION_KINDS})\b"
)
NAMESPACE = re.compile(rf"^namespace\s+({LEAN_NAME})\s*$")
SECTION = re.compile(rf"^(?:noncomputable\s+)?section(?:\s+({LEAN_NAME}))?\s*$")
END = re.compile(rf"^end(?:\s+({LEAN_NAME}))?\s*$")
IMPORT = re.compile(r"^[ \t]*(?:public\s+)?import\s+([^\n]+)", re.MULTILINE)


@dataclass(frozen=True)
class Declaration:
    module: str
    path: str
    line: int
    kind: str
    name: str


@dataclass(frozen=True)
class Scope:
    kind: str
    label: str | None
    namespace_before: str
    namespace_after: str
    line: int


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


def qualify(name: str, namespace: str) -> str:
    """Apply the project's explicit relative-name or `_root_.` convention."""
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    return f"{namespace}.{name}" if namespace else name


def in_project_namespace(name: str) -> bool:
    return name == PROJECT_NAMESPACE or name.startswith(f"{PROJECT_NAMESPACE}.")


def inventory_source(module: str, path: str, code: str) -> tuple[list[Declaration], list[str]]:
    """Inventory supported declaration commands without parsing or executing Lean.

    Namespace and section commands must occupy their own lines. Attributes may
    occupy preceding lines or precede a declaration on its line. A bracket
    counter handles multiline attributes after comments and strings are blanked.
    Unsupported names/scope commands fail visibly instead of disappearing from
    the inventory. Anonymous sections may remain open at the end of a file, as
    in the project's `noncomputable section` convention.

    Generated constructors, projections, recursors, and local proof terms are
    not separate source declaration commands and are not enumerated here.
    """
    declarations: list[Declaration] = []
    errors: list[str] = []
    scopes: list[Scope] = []
    namespace = ""
    saw_namespace = False
    attribute_depth = 0
    attribute_line = 0

    def error(line: int, message: str) -> None:
        errors.append(f"{path}:{line}: {message}")

    for line_number, raw_line in enumerate(code.splitlines(), 1):
        line = raw_line.strip()
        # Attributes are retained by code_only, so trust-policy token checks
        # still inspect them. Only the declaration inventory removes them.
        while attribute_depth or line.startswith("@["):
            if not attribute_depth:
                attribute_line = line_number
                attribute_depth = 1
                line = line[2:]
            stop = None
            for index, char in enumerate(line):
                if char == "[":
                    attribute_depth += 1
                elif char == "]":
                    attribute_depth -= 1
                    if attribute_depth == 0:
                        stop = index + 1
                        break
            if stop is None:
                line = ""
                break
            line = line[stop:].lstrip()
        if not line:
            continue

        if match := NAMESPACE.fullmatch(line):
            label = match.group(1)
            target = qualify(label, namespace)
            if not in_project_namespace(target):
                error(line_number, f"unexpected namespace {target!r}")
            scopes.append(Scope("namespace", label, namespace, target, line_number))
            namespace = target
            saw_namespace = True
            continue

        if match := SECTION.fullmatch(line):
            scopes.append(Scope("section", match.group(1), namespace, namespace, line_number))
            continue

        if match := END.fullmatch(line):
            if not scopes:
                error(line_number, "end without a corresponding namespace or section")
                continue
            scope = scopes.pop()
            supplied = match.group(1)
            accepted = {scope.label}
            if scope.kind == "namespace":
                accepted.add(scope.namespace_after)
            if supplied is not None and supplied not in accepted:
                error(line_number, f"end {supplied!r} does not close {scope.kind} "
                    f"{scope.label!r} opened on line {scope.line}")
            namespace = scope.namespace_before
            continue

        if re.match(r"^(?:namespace|section|end)\b|^noncomputable\s+section\b", line):
            error(line_number, "unsupported namespace/section/end syntax")
            continue
        if re.match(r"^(?:mutual|export|alias)\b", line):
            error(line_number, "declaration-generating command is outside this source inventory")
            continue

        if match := DECLARATION.match(line):
            if "private" in match.group("modifiers").split():
                error(line_number, "private declarations have generated names; use an explicit "
                    "public declaration for this draft's prepared queries")
                continue
            name = qualify(match.group("name"), namespace)
            if not in_project_namespace(name):
                error(line_number, f"named declaration outside the project namespace: {name!r}")
                continue
            declarations.append(Declaration(module, path, line_number, match.group("kind"), name))
        elif DECLARATION_START.match(line):
            error(line_number, "unsupported or anonymous declaration header; an explicitly named "
                "declaration is required for the source inventory")

    if attribute_depth:
        error(attribute_line, "unclosed leading declaration attribute")
    for scope in scopes:
        if scope.kind == "namespace" or scope.label is not None:
            error(scope.line, f"unclosed {scope.kind} {scope.label!r}")
    if module.startswith(f"{PROJECT_NAMESPACE}.") and not saw_namespace:
        error(1, "implementation module must explicitly enter the project namespace")
    return declarations, errors


def render_axiom_audit(declarations: list[Declaration]) -> str:
    modules = sorted({d.module for d in declarations})
    allowlist = ", ".join(f"`{name}`" for name in STANDARD_AXIOMS)
    lines = [
        "import AmbidextrousSofa", "", "/-!", "# Prepared axiom queries — not executed", "",
        "Regenerate with `python scripts/check_source_policy.py --write-axiom-audit`.",
        f"The source-only inventory lists {len(declarations)} explicitly named declarations",
        f"across {len(modules)} implementation modules, respecting their namespace scopes.",
        "Generated constructors, projections, recursors, and local proof terms are not",
        "separately enumerated by this lexical inventory.", "",
        "The permitted resulting transitive axiom set is a subset of:", f"{allowlist}.", "",
        "These queries have not been executed and do not enforce that policy themselves.",
        "A later Lean verification pass must elaborate the sources, check the proofs,",
        "and inspect the actual transitive axiom output. This file is deliberately",
        "outside the main library entry point.", "-/",
    ]
    for module in modules:
        entries = [d for d in declarations if d.module == module]
        lines.extend(["", f"-- {entries[0].path}"])
        lines.extend(f"#print axioms {d.name}" for d in entries)
    return "\n".join(lines) + "\n"


def inventory_counts(declarations: list[Declaration]) -> dict[str, object]:
    modules = []
    for module in sorted({d.module for d in declarations}):
        entries = [d for d in declarations if d.module == module]
        kinds = Counter(d.kind for d in entries)
        modules.append({
            "module": module,
            "path": entries[0].path,
            "theorems": kinds["theorem"] + kinds["lemma"],
            "declarations": len(entries),
            "kinds": dict(sorted(kinds.items())),
        })
    return {
        "implementation_modules": len(modules),
        "theorems": sum(d.kind in {"theorem", "lemma"} for d in declarations),
        "declarations": len(declarations),
        "modules": modules,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-axiom-audit", action="store_true",
        help="regenerate prepared queries from valid source names; never invokes Lean")
    parser.add_argument("--inventory-json", action="store_true",
        help="emit per-module source counts and policy status as JSON")
    args = parser.parse_args()
    errors: list[str] = []
    source_errors: list[str] = []
    files = sorted(
        p for p in ROOT.rglob("*.lean")
        if not {".git", ".lake"}.intersection(p.relative_to(ROOT).parts)
    )
    if not files:
        errors.append("no project Lean files found")
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in files}
    graph: dict[str, list[str]] = {}
    declarations: list[Declaration] = []
    declaration_names: set[str] = set()
    cleaned: dict[Path, str] = {}
    for module, path in modules.items():
        source = path.read_text(encoding="utf-8")
        label = str(path.relative_to(ROOT))
        try:
            code = code_only(source)
        except ValueError as error:
            source_errors.append(f"{label}: {error}")
            continue
        cleaned[path] = code
        if not source.endswith("\n"):
            source_errors.append(f"{label}: missing final newline")
        if any(line.rstrip() != line for line in source.splitlines()):
            source_errors.append(f"{label}: trailing whitespace")
        identifiers = set(re.findall(r"\b[\w']+\b", code))
        prohibited = identifiers & FORBIDDEN
        if prohibited:
            source_errors.append(f"{label}: prohibited identifiers {sorted(prohibited)}")
        if re.search(r"#(?:eval|reduce|run|compile)\b|debug\.skipKernelTC", code):
            source_errors.append(f"{label}: prohibited evaluation or trust-bypass command")
        imports = [name for row in IMPORT.findall(code) for name in row.split()]
        graph[module] = [name for name in imports
            if name != "Mathlib" and not name.startswith("Mathlib.")]
        for name in imports:
            if name != "Mathlib" and not name.startswith("Mathlib.") and name not in modules:
                source_errors.append(f"{label}: import outside Mathlib/project: {name}")
        entries, scope_errors = inventory_source(module, label, code)
        source_errors.extend(scope_errors)
        if module == "AxiomAudit" and entries:
            source_errors.append("AxiomAudit.lean must contain prepared queries, not new declarations")
        for declaration in entries:
            if declaration.name in declaration_names:
                source_errors.append(f"duplicate named declaration: {declaration.name}")
            declaration_names.add(declaration.name)
            declarations.append(declaration)

    errors.extend(source_errors)
    audit_written = False
    if args.write_axiom_audit:
        if source_errors:
            errors.append("prepared axiom queries were not regenerated because source inventory "
                "or trust-policy checks failed")
        else:
            audit_text = render_axiom_audit(declarations)
            (ROOT / "AxiomAudit.lean").write_text(audit_text, encoding="utf-8")
            cleaned[ROOT / "AxiomAudit.lean"] = code_only(audit_text)
            audit_written = True

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
    missing_queries = declaration_names - set(queries)
    extra_queries = set(queries) - declaration_names
    if missing_queries or extra_queries or len(queries) != len(declarations):
        errors.append("future axiom audit does not cover each named declaration exactly once "
            f"({len(missing_queries)} missing; {len(extra_queries)} stale; "
            f"{len(queries) - len(set(queries))} duplicate queries)")

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
    counts = inventory_counts(declarations)
    if args.inventory_json:
        print(json.dumps({
            "source_policy_passed": not errors,
            "lean_executed": False,
            "axiom_queries_executed": False,
            "axiom_audit_regenerated": audit_written,
            "intended_standard_axioms": STANDARD_AXIOMS,
            "lean_files": len(files),
            **counts,
            "errors": errors,
        }, indent=2))
        return 1 if errors else 0
    if audit_written:
        print(f"Regenerated AxiomAudit.lean with {len(declarations)} unexecuted queries.")
    if errors:
        print("SOURCE POLICY FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"Source policy passed: {len(files)} Lean files; {counts['theorems']} named theorems;")
    print(f"{len(declarations)} named declarations covered by unexecuted axiom queries.")
    print("Imports and dependency pins checked; no CI configuration found.")
    print("No Lean execution occurred. This is not a kernel proof or axiom audit.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
