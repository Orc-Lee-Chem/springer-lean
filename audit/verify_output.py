"""Check the recorded replay types against the single-ramp freeze."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys


AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
NS = "SpringerLean.PaperStatementsAudit."
DEFINITION = re.compile(r"^(SpringerLean\.[\w.]+) : ", re.MULTILINE)
AXIOM_PRINT = re.compile(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]")


def normalize(text):
    return " ".join(text.split())


def printed_types(text):
    positions = list(DEFINITION.finditer(text))
    results = {}
    for i, match in enumerate(positions):
        end = positions[i + 1].start() if i + 1 < len(positions) else len(text)
        declaration = text[match.end():end].split("'SpringerLean.", 1)[0]
        results[match[1]] = normalize(declaration)
    return results


def printed_axioms(text):
    return {
        name: {a.strip() for a in axioms.split(",") if a.strip()}
        for name, axioms in AXIOM_PRINT.findall(text)
    }


def read(path):
    return path.read_text(encoding="utf-8")


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def main():
    logs = Path(sys.argv[1])
    repo = Path(__file__).resolve().parents[1]
    frozen = read(repo / "audit/frozen-paper-statements.txt")
    expected_types = printed_types(frozen)
    expected_axioms = printed_axioms(frozen)
    require(len(expected_types) == len(expected_axioms) == 15,
            "Expected 15 frozen declarations.")
    require(all(n.startswith(NS) for n in expected_types), "Unexpected paper namespace.")
    actual_types = printed_types(read(logs / "types.log"))
    paper = read(logs / "paper.log")
    paper_types = printed_types(paper)
    require(paper_types == expected_types, "The paper types differ from the freeze.")
    require(all(actual_types.get(n) == t for n, t in expected_types.items()),
            "The complete-type export differs from the freeze.")
    actual_axioms = printed_axioms(read(logs / "audit.log"))
    require(printed_axioms(paper) == expected_axioms,
            "The paper axiom output differs from the freeze.")
    require(all(actual_axioms.get(n) == a for n, a in expected_axioms.items()),
            "The separate axiom audit differs from the freeze.")
    require(len(actual_axioms) == 17 and all(a <= AXIOMS for a in actual_axioms.values()),
            "Unexpected transitive axiom set.")
    state = json.loads(read(logs / "initial_state.json"))
    require(state["initial_project_oleans"] == 0, "Project artifacts were present at start.")
    manifest = (repo / "SOURCE_SHA256SUMS.txt").read_bytes()
    manifest_sha = hashlib.sha256(manifest).hexdigest()
    require(manifest_sha == state["source_manifest_sha256"], "Replay used different sources.")
    expected_modules = json.loads(read(repo / "project_modules.json"))
    last_exits = dict(line.split("\t") for line in read(logs / "module_exits.tsv").splitlines()[1:])
    require(set(last_exits) == set(expected_modules) and all(x == "0" for x in last_exits.values()),
            "At least one project module has not passed.")
    actual_gates = json.loads(read(logs / "exit_codes.json"))
    gates = {"root", "paper_module", "paper", "types", "audit"}
    require(set(actual_gates) == gates and all(code == 0 for code in actual_gates.values()),
            "The root, paper, types, or audit gate failed.")
    attempts = Counter(code for _, code in
                       (line.split("\t") for line in read(logs / "module_exits.tsv").splitlines()[1:]))
    lock = json.loads(read(repo / "lean/lake-manifest.json"))
    mathlib = next(p["rev"] for p in lock["packages"] if p["name"] == "mathlib")
    report = {
        "initial_project_oleans": 0,
        "compiled_import_closure_including_root": len(last_exits),
        "module_exit_code_attempt_counts": dict(sorted(attempts.items())),
        "gates": actual_gates,
        "public_declarations_matching_frozen_types_and_axioms": 15,
        "separate_axiom_checks": len(actual_axioms),
        "transitive_axioms": sorted(set().union(*actual_axioms.values())),
        "lean": read(logs / "versions.log").strip(),
        "mathlib_lock": mathlib,
        "source_manifest_sha256": manifest_sha,
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

