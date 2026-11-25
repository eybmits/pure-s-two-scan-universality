# Verification commands and transcripts

The release uses Lean 4.35.0, the Mathlib commit in `lake-manifest.json` and Nanoda 0.4.19. Run these commands from an extracted project root using the dependency-cache instructions in `README.md`. The build project, the Lean replay project and the Nanoda project initially had separate empty local build directories. Only pinned external library caches were reused.

| Command | Captured output |
| --- | --- |
| `lake --quiet build` | [Full clean Lake build including its linter warnings](lake-build.log) |
| `lake env lean verification/Endpoints.lean` | [All nine types and their axioms](endpoint-types.log) |
| `lake env python3 verify.py --fresh --examples` | [Kernel replay](lean-replay.log), followed by [all six examples](examples.log) |
| `python3 check_external.py` | [Independent Nanoda replay and export digest](nanoda.log) |
| `python3 code/pure_s_two_cell.py` | [Standalone two-cell run](two-cell.log) |

Each command exited with status zero. The fresh kernel pass covers the import closures of `Certified`, `Chronology`, `Majority`, `SerialOutput` and `OrbitHardness`. The Lake log includes elapsed times and scheduling-dependent message order. The Nanoda log gives the digest of the reference export and the names the checker returned. The endpoint transcript gives the exact propositions and their axiom reports.
