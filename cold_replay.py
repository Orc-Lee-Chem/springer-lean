"""Elaborate the frozen project sources under the locked Lake environment."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", type=Path)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    project = root / "lean"
    library = project / ".lake/build/lib/lean"
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    module_logs = logs / "modules"
    module_logs.mkdir(exist_ok=True)
    manifest = root / "SOURCE_SHA256SUMS.txt"
    for line in manifest.read_text(encoding="utf-8").splitlines():
        digest, relative = line.split("  ", 1)
        if hashlib.sha256((root / relative).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"Source hash mismatch: {relative}")
    paths = os.environ.get("LEAN_PATH", "").split(os.pathsep)
    if library.resolve() not in {Path(p).resolve() for p in paths if p}:
        raise SystemExit("Run with lake env from the extracted lean directory.")
    modules = json.loads((root / "project_modules.json").read_text(encoding="utf-8"))
    source_hash = hashlib.sha256(manifest.read_bytes()).hexdigest()
    state_path = logs / "initial_state.json"
    record_path = logs / "module_exits.tsv"

    def olean(name):
        return (library / Path(*name.split("."))).with_suffix(".olean")

    completed = set()
    if args.resume:
        state = json.loads(state_path.read_text(encoding="utf-8"))
        if (state["initial_project_oleans"] != 0 or state["project"] != str(project) or
                state["source_manifest_sha256"] != source_hash):
            raise SystemExit("Resume requires the original cold extraction and unchanged sources.")
        for line in record_path.read_text(encoding="utf-8").splitlines()[1:]:
            name, code = line.split("\t")
            if name in modules and code == "0" and olean(name).is_file():
                completed.add(name)
    else:
        initial = len(list(library.rglob("*.olean")))
        if initial or state_path.exists():
            raise SystemExit("Cold replay requires a fresh extraction and a fresh log directory.")
        dump(state_path, {
            "initial_project_oleans": initial, "project": str(project),
            "module_count_including_root": len(modules),
            "source_manifest_sha256": source_hash,
            "start_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        })

    def lean(args, output):
        with output.open("wb") as log:
            return subprocess.run(["lean", *args], cwd=project,
                                  stdout=log, stderr=subprocess.STDOUT).returncode

    if lean(["--version"], logs / "versions.log"):
        return 2

    def build_module(name):
        relative = Path(*name.split("."))
        out = olean(name)
        out.parent.mkdir(parents=True, exist_ok=True)
        return lean(["-j", "1", "-o", str(out), str(relative.with_suffix(".lean"))],
                    module_logs / f"{name}.log")

    todo = {name: deps for name, deps in modules.items() if name not in completed}
    failure = None
    with record_path.open("a" if args.resume else "w", encoding="utf-8", buffering=1) as record:
        if not args.resume:
            record.write("module\texit\n")
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            running = {}
            while todo or running:
                if failure is None:
                    ready = [name for name, deps in todo.items() if set(deps) <= completed]
                    for name in ready[:args.workers - len(running)]:
                        running[pool.submit(build_module, name)] = name
                        del todo[name]
                if not running:
                    if failure is None:
                        raise SystemExit("No module is ready. Check the project import graph.")
                    break
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for result in done:
                    name = running.pop(result)
                    code = result.result()
                    record.write(f"{name}\t{code}\n")
                    if code == 0:
                        completed.add(name)
                    elif failure is None:
                        failure = {"module": name, "exit": code}
                    dump(logs / "sequential_progress.json", {
                        "completed": len(completed), "total": len(modules), "last": name,
                        "last_exit": code, "failure": failure,
                    })
    if failure is not None:
        dump(logs / "failure.json", failure)
        return 1

    exits = {"root": 0}
    paper_module = library / "PaperStatementsAudit.olean"
    exits["paper_module"] = lean(
        ["-j", "1", "-o", str(paper_module), "PaperStatementsAudit.lean"],
        logs / "paper_module.log")
    dump(logs / "exit_codes.json", exits)
    if exits["paper_module"]:
        return 1
    for key, file in (("audit", "Audit.lean"), ("types", "CompleteTypes.lean"),
                      ("paper", "PaperStatementsAudit.lean")):
        exits[key] = lean([file], logs / (key + ".log"))
        dump(logs / "exit_codes.json", exits)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    audits = {}
    for key in ("audit", "types", "paper"):
        source = (logs / (key + ".log")).read_text(encoding="utf-8")
        sets = [set(re.split(r",\s*", match.strip())) for match in
                re.findall(r"depends on axioms: \[([^]]*)\]", source)]
        audits[key] = {"prints": len(sets), "axioms": sorted(set().union(*sets))}
        audits[key]["accepted"] = bool(sets) and all(s <= allowed for s in sets)
    dump(logs / "axiom_audit.json", audits)
    return int(any(exits.values()) or not all(item["accepted"] for item in audits.values()))


if __name__ == "__main__":
    sys.exit(main())
