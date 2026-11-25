"""Build all local proofs from source in a fresh directory and replay them with leanchecker."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from graphlib import TopologicalSorter

from check_external import THEOREMS

ROOT = Path(__file__).resolve().parent
PIN = "56a005855ea17e0b0958f73ec801ae140b0a1679"
VERSION = "4.35.0"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ENDPOINTS = set(THEOREMS)


def command(args, **kwargs):
    return subprocess.run(args, check=True, **kwargs)


def binary(name, directory):
    path = directory / name if directory else shutil.which(name)
    if not path or not Path(path).is_file():
        raise SystemExit(f"Missing {name}. Put the pinned Lean toolchain on PATH or use --lean-bin.")
    return str(Path(path).absolute())


def dependencies(src):
    modules = {p.stem: p for p in sorted(src.glob("*.lean"))}
    graph = {}
    for mod, path in modules.items():
        content = path.read_text(encoding="utf-8")
        imports = re.findall(r"^import\s+([\w.]+)\s*$", content, re.MULTILINE)
        graph[mod] = [m for m in imports if m in modules]
        for m in imports:
            if m not in modules and m != "Std" and not m.startswith("Mathlib."):
                raise SystemExit(f"Missing local dependency {m} imported by {mod}.")
    return list(TopologicalSorter(graph).static_order())


def check(mathlib, lean_dir, fresh):
    lean = binary("lean", lean_dir)
    checker = binary("leanchecker", lean_dir)
    env = dict(os.environ)
    env["PATH"] = str(Path(lean).parent) + os.pathsep + env["PATH"]
    info = command([lean, "--version"], capture_output=True, text=True, env=env).stdout.strip()
    if not re.search(r"\bversion " + re.escape(VERSION) + r"\b", info):
        raise SystemExit(f"Expected Lean {VERSION}, got {info}.")
    print(info, flush=True)
    revision = command(["git", "-C", str(mathlib), "rev-parse", "HEAD"],
                       capture_output=True, text=True).stdout.strip()
    if revision != PIN:
        raise SystemExit(f"Expected Mathlib {PIN}, got {revision}.")
    print(f"Mathlib {revision}", flush=True)
    compiled = mathlib / ".lake/build/lib/lean"
    if not (compiled / "Mathlib/Computability/TuringMachine/ToPartrec.olean").is_file():
        raise SystemExit("Install the Mathlib cache first. See README.md.")
    imports = sorted(mathlib.glob(".lake/packages/*/.lake/build/lib/lean"))
    # Lake in a new project may install Mathlib and its dependencies as siblings.
    if mathlib.parent.name == "packages":
        imports += sorted(mathlib.parent.glob("*/.lake/build/lib/lean"))
    modules = dependencies(ROOT / "formal")
    with tempfile.TemporaryDirectory(prefix="pure-s-verify-") as folder:
        build = Path(folder)
        env["LEAN_PATH"] = os.pathsep.join(map(str, [build, compiled, *imports]))
        seen = set()
        for mod in modules:
            name = mod + ".lean"
            shutil.copyfile(ROOT / "formal" / name, build / name)
            print(f"Building {mod}", flush=True)
            p = subprocess.run([lean, "-o", mod + ".olean", name], cwd=build, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if p.returncode:
                print(p.stdout, file=sys.stderr)
                p.check_returncode()
            if "sorryAx" in p.stdout or "declaration uses 'sorry'" in p.stdout:
                raise SystemExit(f"Unproved declaration reported by Lean in {mod}.")
            for theorem, axioms in re.findall(r"'([\w.]+)' depends on axioms:\s*\[([^\]]*)\]", p.stdout):
                actual = {s.strip() for s in axioms.split(",") if s.strip()}
                if actual - STANDARD_AXIOMS:
                    raise SystemExit(f"Unexpected axioms for {theorem}: {sorted(actual)}.")
                if theorem in ENDPOINTS:
                    print(f"{theorem} axioms: {', '.join(sorted(actual))}", flush=True)
                    seen.add(theorem)
        for mod in modules:
            print(f"Kernel replay {mod}", flush=True)
            command([checker, mod], cwd=build, env=env)
        if ENDPOINTS - seen:
            raise SystemExit(f"Missing axiom reports for {sorted(ENDPOINTS - seen)}.")
        if fresh:
            for endpoint in ("Certified", "Chronology", "Majority", "SerialOutput", "OrbitHardness"):
                print(f"Fresh transitive kernel replay of {endpoint}.", flush=True)
                command([checker, "--fresh", "--verbose", endpoint], cwd=build, env=env)
        print(f"PASS: {len(modules)} source modules compiled and replayed; {len(ENDPOINTS)} endpoints checked.",
              flush=True)


def examples():
    for name in ("replay", "output", "reference", "guided", "prefix", "two_cell"):
        script = ROOT / "code" / f"pure_s_{name}.py"
        print(f"Running {script.name}", flush=True)
        command([sys.executable, "-B", str(script)], cwd=ROOT)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, default=ROOT / ".lake/packages/mathlib",
                        help="pinned Mathlib checkout with its dependency caches")
    parser.add_argument("--lean-bin", type=Path, help="directory containing lean and leanchecker")
    parser.add_argument("--examples", action="store_true", help="also run the small Python examples")
    parser.add_argument("--fresh", action="store_true", help="also replay the import closures of Certified, Chronology, Majority, SerialOutput, and OrbitHardness in separate empty kernel environments")
    args = parser.parse_args()
    check(args.mathlib.resolve(), args.lean_bin.resolve() if args.lean_bin else None, args.fresh)
    if args.examples:
        examples()
