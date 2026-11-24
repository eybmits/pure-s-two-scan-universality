# Two scans in pure S

**Markus Baumann** · [Three-page paper](paper/main.pdf) · [Formal theorem](formal/Certified.lean)

A finite tree whose only leaf is S generates candidate computation histories. Two routes through the same candidate run at different speeds. Their relative delay aligns corresponding cells in adjacent tape rows. A fixed finite tree automaton detects a consistent halting history, and a fixed decoder reads its last row.

## What Lean proves

For every partial computable function on binary strings there is a finite program string `p`. For every input `x` and output `y`, reduction of the ground seed for `p,x` reaches a snapshot decoding to `some y` exactly when the function returns `y` at `x`. This includes empty outputs and excludes spurious hits on divergent inputs. The same encoder, detector and decoder serve every program.

The primary theorem uses maximal parallel innermost rounds of the rule `S x y z → (x z) (y z)`. Seed size is linear in the input and program lengths. The decoder emits at most two bits per S leaf in a snapshot. For every regular output language, its inverse image under this decoder is a regular tree language, including on malformed trees. A second theorem implements first-hit observation along a fixed left-to-right order of individual contractions. Its seed contains two copies, and its detector requires both to pass.

The proof obtains one finite universal transition table from Mathlib's universal evaluator. The table is selected by an existence proof. The Lean definitions expose the encoder, reporter, and decoder parametrically in the table. The small Python examples use a compact coding for demonstrations. Instantiating the library's full universal table as a practical emulator is outside the artifact's claims.

## Reproduce the result

Install [Elan](https://github.com/leanprover/elan) and Python 3.10 or later. From the repository root, obtain the pinned library cache and run the complete check.

```sh
lake exe cache get Mathlib.Computability.Halting Mathlib.Computability.PartrecCode Mathlib.Computability.Reduce Mathlib.Computability.StateTransition Mathlib.Computability.TuringMachine.PostTuringMachine Mathlib.Computability.TuringMachine.ToPartrec Mathlib.Data.Fintype.EquivFin
lake env python3 verify.py
```

The checker builds every local source in a new temporary directory, verifies the main theorem's axiom report and replays every local module with Lean's kernel. The expected final line starts with `PASS`. The toolchain is Lean 4.35.0. The manifest pins Mathlib to [56a005855ea17e0b0958f73ec801ae140b0a1679](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679). The endpoint uses `propext`, `Classical.choice` and `Quot.sound`. The [verification record](verification.txt) reports the release checks.

To check the main theorem, serial theorem and undecidability corollary with the independent Rust kernel Nanoda, run the following command after installing the cache. It builds the endpoints, exports their proofs, checks the three-axiom allowlist, and verifies that the checker returned all three requested theorem names.

```sh
python3 check_external.py
```

For editor use, `lake build` builds the entire project. With an existing cached checkout, run `python3 verify.py --mathlib PATH_TO_MATHLIB --lean-bin PATH_TO_LEAN_BIN`. Add `--fresh` to replay the main theorem and all imported declarations in an empty kernel environment. Add `--examples` to run the Python demonstrations too. With LaTeX installed, `latexmk -pdf -cd paper/main.tex` rebuilds the paper.

## Where to check the argument

| Question | Formal source |
| --- | --- |
| What exactly is an S step or a round? | [Ground trees and the S rule](formal/Anchors.lean), [parallel innermost reduction](formal/Frames.lean) |
| Can a stray subtree impersonate a generated candidate? | [Exact correspondence between tagged packets and their origins](formal/Shell.lean) |
| Do the two scans really compare cells one chosen width apart? | [Native scan tests and their equivalence](formal/JoinGate.lean) |
| Can a candidate skip a row or use a different input? | [Alignment of the immediate successors](formal/Tableau.lean), [uniqueness of the input suffix](formal/ShellAnyInput.lean) |
| Does each reported value come from a genuine halt? | [Arbitrary starting tape](formal/ShellAnyTape.lean), [fixed universal machine and every hit](formal/UniversalS.lean) |
| Could the external readout perform the simulation? | [Regular inverse images for the concrete decoder](formal/OutputPreimage.lean), [output-size bound](formal/ReadPostBound.lean) |
| How are arbitrary strings, including trailing zeros, preserved? | [Sentinel coding](formal/StringCoding.lean), [raw bit-string input](formal/BinaryInput.lean), [witnesses](formal/Prize.lean) |
| Does this work along actual individual contractions? | [Scheduled path and first hit](formal/SerialReadout.lean), [serial universality](formal/SerialOutput.lean) |
| How hard is predicting a hit? | [Many-one completeness and undecidability on the family of seeds indexed by program and input](formal/OrbitHardness.lean) |
| What happens on a simple total function or on an infinite loop? | [Ground-term echo and divergence examples](formal/TableauExamples.lean) |

The generator and tag develop Appendices I and L of the author's *Pure S Complete Research Dossier*. OpenAI Codex assisted with proof development, testing and manuscript preparation. The formulation uses the fixed-strategy, feature-detection interpretation discussed in [Wolfram's challenge announcement](https://writings.stephenwolfram.com/2021/06/1920-2020-and-a-20000-prize-announcing-the-s-combinator-challenge/).

Alexander Filin previously described a different pure-S construction with a [root-restarted finite controller](https://cinematicstrawberry.com/00110000/articles/scombinator.html). The present construction fixes maximal parallel innermost reduction and compares adjacent rows of generated histories.
