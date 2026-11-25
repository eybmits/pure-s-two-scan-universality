# Universal Computation with the S Combinator under Parallel Innermost Reduction

**Markus Baumann** · [Paper with technical appendix](paper/main.pdf) · [Formal theorem](formal/Certified.lean) · [Proof archive embedded in the paper](paper/pure-s-lean-proof.zip)

Wolfram proposed reading a computed answer from a growing S-tree with a bounded observer. This construction realizes that formulation along a fixed evaluation path for every partial computable function on binary strings. Changing programs changes only the seed. Under parallel innermost reduction the tree generates candidate histories of one fixed universal machine. Two scans driven by the S rule align corresponding cells in successive rows at any row width. A fixed finite tree automaton checks the machine’s local transition rule on those cells and detects a valid halting history. A fixed decoder reads the output from its last row.

## Submission files

The [submission folder](submission/) contains the [manuscript](submission/Pure_S_Universality.pdf), [cover letter](submission/Pure_S_Submission.txt) and [reproducibility archive](submission/Pure_S_Universality_Reproducibility.zip). Run `shasum -a 256 -c SHA256SUMS` from the repository root to verify all three files.

The [LaTeX source](paper/main.tex) builds with `latexmk -cd -pdf paper/main.tex`. The [proof audit](TCB_AUDIT.md) gives the Lean and Nanoda replay commands.

## What Lean proves

For every partial computable function on binary strings there is a finite program string `p`. For every input `x` and output `y`, reduction of the ground seed for `p,x` reaches a snapshot decoding to `some y` exactly when the function returns `y` at `x`. This includes empty outputs and excludes spurious hits on divergent inputs. The same encoder, detector and decoder serve every program.

The primary theorem uses maximal parallel innermost rounds of the rule `S x y z → (x z) (y z)`. Seed size is linear in the input and program lengths. With fixed finite tables, encoding takes linear time in the combined program and input length, plus constant overhead. On an expanded N-node tree, detection and extraction can each run in O(N) time. One bottom-up pass marks passing packets, a single path selects one, and a fixed number of scans reads its word and row. The decoder emits at most two bits per S leaf in a snapshot. For every regular output language, its inverse image under this decoder is a regular tree language, including on malformed trees. A second theorem implements first-hit observation along a fixed left-to-right order of individual contractions. Its seed contains two copies. After each contraction, a finite tree automaton tests whether both pass. At the first such step the decoder returns the output of the left copy. A three-copy variant accepts when all three detectors pass. At any single-contraction snapshot, at least two copies are at parallel round boundaries. Their outputs agree whenever all three pass, so reading the majority gives the correct string at every detection. On arbitrary trees the detection predicate is regular. The regular-preimage theorem above concerns the original parallel decoder.

A fixed finite tree automaton detects whether a snapshot contains a passing prefix packet, including on a run that continues forever. For a fixed deterministic one-tape transition table, every configuration returned by the indexed reader agrees with the indicated machine step up to blank padding. For each finite horizon, arbitrarily late parallel rounds contain a single history from which the reader recovers all rows through that horizon.

A separate linear-size seed allows one fixed reader for that transition table to recover the configurations successively. This reader compares the row counts of passing packets and obtains a row index by counting differences between two clock copies in the current tree. Serialize each parallel round by contracting its original innermost redexes from left to right. At contraction index zero the reader returns the initial row. There is one strictly increasing sequence of individual contraction indices along which it returns every successive step number and its canonical tape row. Redundant blanks beyond the head are removed. Every other reported pair is also correct. The linear snapshot-time bound above concerns the binary-string output decoder.

The proof obtains one finite universal transition table from Mathlib's universal evaluator. The table is selected by an existence proof. The Lean definitions expose the encoder, reporter, and decoder parametrically in the table. The small Python examples use a compact coding for demonstrations. Instantiating the library's full universal table as a practical emulator is outside the artifact's claims.

The paper also carries a PDF attachment, `pure-s-lean-proof.zip`, containing the proof and replay instructions. The same attachment is in `paper/` so the PDF can be rebuilt from this package. This package contains 81 modules, including seven for chronological readout and one for the three-copy construction.

The [formal proof audit](TCB_AUDIT.md) maps the semantics to source lines, gives all nine Lean statements and records the two independent verification commands.

## Reproduce the result

Install [Elan](https://github.com/leanprover/elan) and Python 3.10 or later. From the repository root, obtain the pinned library cache and run the complete check.

```sh
lake exe cache get Mathlib.Computability.Halting Mathlib.Computability.PartrecCode Mathlib.Computability.Reduce Mathlib.Computability.StateTransition Mathlib.Computability.TuringMachine.PostTuringMachine Mathlib.Computability.TuringMachine.ToPartrec Mathlib.Data.Fintype.EquivFin
lake env python3 verify.py
```

The checker builds all 81 local modules from source in a new temporary directory, inspects the theorem axiom reports and replays each module with Lean's kernel. The expected final line starts with `PASS`. The toolchain is Lean 4.35.0. The manifest pins Mathlib to [56a005855ea17e0b0958f73ec801ae140b0a1679](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679). The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The [verification record](verification.txt) reports the release checks.

To check all nine statements with Nanoda, the independent Rust proof checker, run the command below after installing the cache. The script builds the relevant modules, exports the proofs and their dependencies, enforces the three-axiom allowlist and requires Nanoda to return all nine theorem names.

```sh
python3 check_external.py
```

For editor use, `lake build` builds the entire project. With an existing cached checkout, run `python3 verify.py --mathlib PATH_TO_MATHLIB --lean-bin PATH_TO_LEAN_BIN`. Add `--fresh` to replay the main theorem and all imported declarations in an empty kernel environment. Add `--examples` to run the Python demonstrations too. With LaTeX installed, `latexmk -pdf -cd paper/main.tex` rebuilds the paper.

## Run the two-cell example

Run `python3 code/pure_s_two_cell.py` from the package directory. Starting at the launch of a hand-built packet, the script applies actual parallel innermost rounds to a shared representation of the ground tree and reads two successive tape rows. A second packet has a forged final row. Its local records and fast scan pass, so the delayed scan is what rejects it. The packet is supplied explicitly in this demonstration. The theorem also proves that the universal seed generates eligible packets.

## Statements checked by Nanoda

| Result | Lean declaration |
| --- | --- |
| Universal binary-string computation under parallel innermost reduction | `TwoScans.Certified.universality` |
| Universal binary-string computation under serial first detection | `TwoScans.Prize.serial_universal_strings` |
| Sound output at every individual serialized detection | `TwoScans.Majority.universal_strings` |
| Many-one completeness of indexed reachability | `TwoScans.OrbitHardness.complete_indexed` |
| Regular detection of a passing computation packet | `TwoScans.TraceReadout.regular_detection` |
| Soundness of the indexed row reader | `TwoScans.TraceSelect.readAt_sound` |
| Recovery of every finite prefix in arbitrarily late parallel rounds | `TwoScans.TraceSelect.readAt_cofinal` |
| One increasing sequence of serial samples for the entire run | `TwoScans.Chronology.trajectory` |
| Linear size of the chronology seed for a fixed machine alphabet | `TwoScans.Chronology.linear_seed` |

## Why the two scans use parallel rounds

The nonregularity observation concerns an unaligned stream of row records. Fix the head position and a machine that enters its halting state in one step while preserving the tape. At a given width the first-row records can describe any of the `2^k` settings of `k` tape bits. For two different settings, appending the matching final row of the first makes the shift test succeed only for that setting. A word automaton with fixed memory cannot distinguish these prefixes for every width. In the tree supplied to the detector, native reductions have already aligned the cells.

The serial results finish the sites selected at the start of each round. A policy that recomputes the leftmost innermost site after every contraction behaves differently on this generator. The left renewal exposes a fresh generator with an unbounded parallel run, which can be serialized. Distinct innermost contractions occur at disjoint sites and commute. By induction on the length of a reduction to an innermost normal form, if one innermost reduction terminates then every maximal innermost reduction has that same finite length. The left operand therefore keeps the recomputed leftmost policy occupied and its right sibling never advances.

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
| How does a reader recover intermediate configurations? | [Prefix correctness](formal/TraceReadout.lean), [indexed selection](formal/TraceSelect.lean), [individual contraction indices](formal/SerialTrace.lean), [canonical tape rows and chronology](formal/Chronology.lean) |
| How hard is predicting a hit? | [Many-one completeness and undecidability on the family of seeds indexed by program and input](formal/OrbitHardness.lean) |
| What happens on a simple total function or on an infinite loop? | [Ground-term echo and divergence examples](formal/TableauExamples.lean) |

The generator and tag develop Appendices I and L of the author's *Pure S Complete Research Dossier*. Markus Baumann directed the research. OpenAI Codex assisted extensively with proof development, Lean formalization and drafting the manuscript. It also assisted with testing. The formulation uses the weaker deterministic alternative discussed in [Wolfram's challenge announcement](https://writings.stephenwolfram.com/2021/06/1920-2020-and-a-20000-prize-announcing-the-s-combinator-challenge/).

In an earlier construction coordinated by Alexander Filin, a finite controller restarts at the root to select each contraction. Theorem 1R gives exact cyclic-tag checkpoints. Corollary 2.2 gives ordered samples of the literal source rows for each defined finite prefix. Here the source for the chronology theorem is a fixed deterministic one-tape machine, and the order of contractions is the left-to-right serialization of parallel innermost reduction. [Filin, Theorem 1R and Corollary 2.2](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/output/pdf/pure_s_universality.pdf)
