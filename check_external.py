"""Recheck the three main theorems and their dependencies with the external Rust kernel Nanoda."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


PROJECT = Path(__file__).resolve().parent
THEOREMS = {
    "Certified": "TwoScans.Certified.universality",
    "SerialOutput": "TwoScans.Prize.serial_universal_strings",
    "OrbitHardness": "TwoScans.OrbitHardness.complete_indexed",
}
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def check(project, lake, exporter, checker):
    def run(args, **kwargs):
        return subprocess.run([lake, *args], cwd=project, check=True, **kwargs)

    try:
        run(["--quiet", "--reconfigure", "build", *["+" + mod for mod in THEOREMS]],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    except subprocess.CalledProcessError as error:
        print(error.stdout, file=sys.stderr)
        raise SystemExit(error.returncode) from error
    version = run(["env", checker, "--help"], capture_output=True, text=True).stdout.splitlines()[0]
    with tempfile.TemporaryDirectory(prefix="pure-s-external-") as scratch:
        folder = Path(scratch)
        exported = folder / "proof.ndjson"
        config = folder / "nanoda.json"
        statements = folder / "statements.txt"
        statements.touch()
        with exported.open("wb") as proof:
            run(["env", exporter, *THEOREMS, "--", *THEOREMS.values()], stdout=proof)
        config.write_text(json.dumps({
            "export_file_path": str(exported),
            "permitted_axioms": AXIOMS,
            "unpermitted_axiom_hard_error": True,
            "nat_extension": True,
            "string_extension": True,
            "pp_declars": list(THEOREMS.values()),
            "pp_output_path": str(statements),
            "pp_options": {"proofs": False, "width": 100},
            "print_success_message": True,
        }), encoding="utf-8")
        print(version, flush=True)
        run(["env", checker, str(config)])
        found = set(re.findall(r"^theorem\s+(\S+)\s*:", statements.read_text(encoding="utf-8"), re.M))
        expected = set(THEOREMS.values())
        if found != expected:
            raise SystemExit(f"Unexpected theorems returned by the checker: {sorted(found)}")
        digest = hashlib.sha256()
        with exported.open("rb") as proof:
            for chunk in iter(lambda: proof.read(1 << 20), b""):
                digest.update(chunk)
        print(f"Proof export SHA-256 {digest.hexdigest()} ({exported.stat().st_size} bytes)")
        print("Certified theorem names:", *THEOREMS.values(), sep="\n  ")
        print("Axiom allow-list:", ", ".join(AXIOMS))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=PROJECT, help="directory containing lakefile.lean")
    parser.add_argument("--lake", default="lake", help="Lake executable for the pinned Lean toolchain")
    parser.add_argument("--exporter", default="leanexport", help="Lean proof exporter executable")
    parser.add_argument("--checker", default="nanoda_bin", help="Nanoda checker executable")
    args = parser.parse_args()
    check(args.project.resolve(), args.lake, args.exporter, args.checker)
