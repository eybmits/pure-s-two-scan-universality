# Direct Simulation of Turing Machines by Parallel Innermost S-Reduction

**Markus Baumann** · [Read the paper (PDF)](direct-emulation/Direct_S_Emulation.pdf)

Under a fixed parallel innermost strategy, a term built from the S combinator and application produces successive configurations of a deterministic Turing machine. Each next configuration appears inside the subtree that encoded its predecessor. A fixed finite-state reader locates the checkpoints, including on infinite runs.

## Direct emulation

The [submission folder](direct-emulation/) contains the three files that belong together.

| File | Contents |
| --- | --- |
| [Manuscript](direct-emulation/Direct_S_Emulation.pdf) | Six-page paper with the construction and proof outline. |
| [Proof archive](direct-emulation/Direct_S_Emulation_Proof.zip) | Lean and LaTeX sources, verification logs, replay instructions and a runnable example. |
| [Cover letter](direct-emulation/Submission.txt) | Submission statement and relation to the earlier paper. |

To see three machine steps, run these commands from the repository root with Python 3.10 or later.

```sh
demo_dir=$(mktemp -d)
unzip -q direct-emulation/Direct_S_Emulation_Proof.zip -d "$demo_dir"
cd "$demo_dir"
python3 canonical_demo.py
```

For the full proof replay, follow `verification/REPLAY.md` inside the extracted archive. It specifies the Lean 4.35.0 and Nanoda 0.4.19 toolchains. To verify the distributed files against the repository manifest, run `shasum -a 256 -c SHA256SUMS` from the checkout root.

## Earlier two-scan paper

[*Universal Computation with the S Combinator under Parallel Innermost Reduction*](submission/Pure_S_Universality.pdf) establishes input–output universality by generating candidate computation histories and aligning tape cells for a finite-state check. The [two-scan guide](TWO_SCAN.md) documents the proof sources in `formal/`, the examples and the verification workflow for that paper.
