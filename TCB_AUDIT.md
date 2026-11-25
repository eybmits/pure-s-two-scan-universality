# Formal proof audit

Lean 4.35.0 and Nanoda 0.4.19 check the same nine propositions. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The definitions below specify the meaning of the propositions. Their implementations and proofs are in the archive. The paper separately derives its time bounds for the external interfaces on expanded trees.

| Concept | Declaration | Source |
| --- | --- | --- |
| Ground syntax | `TwoScans.Term` | [formal/Anchors.lean:5](formal/Anchors.lean#L5) |
| Single contraction in context | `TwoScans.Step` | [formal/Anchors.lean:17](formal/Anchors.lean#L17) |
| Number of leaves | `TwoScans.size` | [formal/Anchors.lean:107](formal/Anchors.lean#L107) |
| Parallel innermost round | `TwoScans.Frames.pi` | [formal/Frames.lean:15](formal/Frames.lean#L15) |
| Frozen left-to-right frontier | `SerialTableau.sweep_is_single_steps` | [formal/Serial.lean:98](formal/Serial.lean#L98) |
| Raw tree recognition | `TwoScans.Automata.Regular` | [formal/ShellAutomata.lean:57](formal/ShellAutomata.lean#L57) |
| Finite word attribute | `TwoScans.WordRead.Attr` | [formal/WordRead.lean:7](formal/WordRead.lean#L7) |
| Binary program and input | `TwoScans.Prize.encodeBits` | [formal/Prize.lean:12](formal/Prize.lean#L12) |
| Final string decoder | `TwoScans.Prize.readStrings` | [formal/Prize.lean:21](formal/Prize.lean#L21) |
| Two-copy constructor | `SerialTableau.pack` | [formal/Serial.lean:111](formal/Serial.lean#L111) |
| Two-copy snapshot reader | `TwoScans.SerialReadout.double` | [formal/SerialReadout.lean:71](formal/SerialReadout.lean#L71) |
| First detection on a finite path prefix | `TwoScans.SerialReadout.readFirst` | [formal/SerialReadout.lean:87](formal/SerialReadout.lean#L87) |
| Three-copy constructor | `TwoScans.Majority.triple` | [formal/Majority.lean:8](formal/Majority.lean#L8) |
| Three-copy snapshot reader | `TwoScans.Majority.read` | [formal/Majority.lean:15](formal/Majority.lean#L15) |
| Program-index encoder | `TwoScans.UniversalS.encodePost` | [formal/UniversalS.lean:24](formal/UniversalS.lean#L24) |
| Program-index reporter | `TwoScans.UniversalS.readPost` | [formal/UniversalS.lean:27](formal/UniversalS.lean#L27) |
| Indexed orbit hit | `TwoScans.OrbitHardness.Hit` | [formal/OrbitHardness.lean:11](formal/OrbitHardness.lean#L11) |
| Sentinel string coding | `TwoScans.StringCoding.pack` | [formal/StringCoding.lean:13](formal/StringCoding.lean#L13) |
| Natural-number partial recursiveness | `Nat.Partrec` | [Partrec.lean:157](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Partrec.lean#L157) |
| Partial recursiveness on encoded types | `Partrec` | [Partrec.lean:231](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Partrec.lean#L231) |
| Program codes | `Nat.Partrec.Code` | [PartrecCode.lean:75](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/PartrecCode.lean#L75) |
| Universal program evaluation | `Nat.Partrec.Code.eval` | [PartrecCode.lean:459](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/PartrecCode.lean#L459) |
| Codes for partial recursive functions | `Nat.Partrec.Code.exists_code` | [PartrecCode.lean:531](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/PartrecCode.lean#L531) |

## Reading the statements

In `Certified.universality`, the finite machine is chosen before the function. Its `encodeBits` seed and `readStrings` decoder appear in the statement. Only the program string depends on the function, and the same program works for every input.

`Prize.serial_universal_witness` names the seed with two copies and the reader `double`. It gives a regular per-snapshot test for each regular output property. Its input–output guarantee uses the first detection on the serialized sweep. `Majority.universal_witness` names the three-copy seed and the reader `Majority.read`. Every detection on that sweep gives the right output. Its detector has a regular domain. The majority decoder compares strings.

`OrbitHardness.concrete_indexed` fixes the seed as `encodePost` and accepts precisely when `readPost` returns an output. It proves many-one completeness on program-index and numerical-input pairs. The chronology result uses its own reader and an increasing sequence of observation times.

## Replay

From the extracted directory, first install the pinned dependencies using the cache command in [README.md](README.md). Then run either line below independently. The first builds all modules, prints all endpoint types and axiom dependencies, replays the Lean kernel and runs the six examples. The second builds the export and verifies it in the Rust checker.

```sh
lake --quiet build && lake env lean verification/Endpoints.lean && lake env python3 verify.py --fresh --examples
python3 check_external.py
```

The two-cell example also runs alone with `python3 code/pure_s_two_cell.py`. [Exact commands and captured outputs](verification/commands.md) include the build and the demo. Nanoda checked the reference export with SHA-256 `9e5554e323e2ca96052460c1572b0e86b611a107330c505807dccf11506ec57d`. From the directory containing the distributed ZIP and its sidecar, `shasum -a 256 -c pure-s-lean-proof.zip.sha256` checks the archive itself. The outer package also records the archive digest in `verification/attachment-replay.txt`.

<details>
<summary>All nine exact Lean types and their axiom reports (expand)</summary>

These are the outputs of `#check` and `#print axioms` in [Endpoints.lean](verification/Endpoints.lean), with fully qualified constants. Expand the file's source if your reader hides disclosure sections. The same [plain-text transcript](verification/endpoint-types.log) is available separately.

```lean
TwoScans.Certified.universality :
  ∃ (P : Type) (fp : TwoScans.Automata.FinStates P) (dp : DecidableEq P) (st : Inhabited P) (M :
    Turing.TM0.Machine TwoScans.UniversalS.Cell P) (a : ℕ) (b : ℕ),
    (TwoScans.Automata.Regular fun (t : TwoScans.Term) =>
        ∃ (y : List Bool), TwoScans.Prize.readStrings M t = Option.some y) ∧
      (∀ (q : List Bool → Bool),
          TwoScans.WordRead.Attr q →
            TwoScans.Automata.Regular fun (t : TwoScans.Term) =>
              ∃ (y : List Bool), TwoScans.Prize.readStrings M t = Option.some y ∧ q y = Bool.true) ∧
        (∀ (t : TwoScans.Term) (y : List Bool),
            TwoScans.Prize.readStrings M t = Option.some y → y.length ≤ 2 * TwoScans.size t) ∧
          (∀ (p x : List Bool), TwoScans.size (TwoScans.Prize.encodeBits P p x) ≤ a + b * (p.length + x.length)) ∧
            ∀ (f : List Bool →. List Bool),
              Partrec f →
                ∃ (p : List Bool),
                  ∀ (x y : List Bool),
                    (∃ (n : ℕ),
                        TwoScans.Prize.readStrings M (TwoScans.Frames.rounds n (TwoScans.Prize.encodeBits P p x)) =
                          Option.some y) ↔
                      y ∈ f x
'TwoScans.Certified.universality' depends on axioms: [propext, Classical.choice, Quot.sound]
TwoScans.Prize.serial_universal_witness :
  ∃ (P : Type) (fp : TwoScans.Automata.FinStates P) (dp : DecidableEq P) (st : Inhabited P) (M :
    Turing.TM0.Machine TwoScans.UniversalS.Cell P) (a : ℕ) (b : ℕ),
    have E := TwoScans.Prize.encodeBits P;
    have D := TwoScans.Prize.readStrings M;
    have start := fun (p x : List Bool) => SerialTableau.pack (E p x) (E p x);
    (TwoScans.Automata.Regular fun (t : TwoScans.Term) =>
        ∃ (y : List Bool), TwoScans.SerialReadout.double D t = Option.some y) ∧
      (∀ (q : List Bool → Bool),
          TwoScans.WordRead.Attr q →
            TwoScans.Automata.Regular fun (t : TwoScans.Term) =>
              ∃ (y : List Bool), TwoScans.SerialReadout.double D t = Option.some y ∧ q y = Bool.true) ∧
        (∀ (p x : List Bool), TwoScans.size (start p x) ≤ a + b * (p.length + x.length)) ∧
          ∀ (f : List Bool →. List Bool),
            Partrec f →
              ∃ (p : List Bool),
                ∀ (x y : List Bool),
                  (∃ (n : ℕ),
                      TwoScans.SerialReadout.readFirst (TwoScans.SerialReadout.double D) (start p x) n =
                        Option.some y) ↔
                    y ∈ f x
'TwoScans.Prize.serial_universal_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
TwoScans.OrbitHardness.concrete_indexed :
  ∃ (P : Type) (fp : TwoScans.Automata.FinStates P) (dp : DecidableEq P) (st : Inhabited P) (M :
    Turing.TM0.Machine TwoScans.UniversalS.Cell P),
    have O := fun (t : TwoScans.Term) => ∃ (out : List Bool), TwoScans.UniversalS.readPost M t = Option.some out;
    have ev := TwoScans.OrbitHardness.Hit (TwoScans.UniversalS.encodePost P) O;
    TwoScans.Automata.Regular O ∧
      REPred ev ∧
        ¬ComputablePred ev ∧
          (∀ (r : ℕ → Prop), REPred r → r ≤₀ ev) ∧
            ∀ (c : TwoScans.UniversalS.Code) (x : ℕ), ev (c, x) ↔ (Nat.Partrec.Code.eval c x).Dom
'TwoScans.OrbitHardness.concrete_indexed' depends on axioms: [propext, Classical.choice, Quot.sound]
TwoScans.TraceReadout.regular_detection {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [TwoScans.Automata.FinStates Q]
  [TwoScans.Automata.FinStates Γ] (δ : TwoScans.Tableau.OneTape.Table Q Γ) (blank : Γ) (accept : Q → Bool) :
  TwoScans.Automata.Regular fun (t : TwoScans.Term) =>
    ∃ (raw : List Bool), TwoScans.TraceReadout.Passing δ blank accept raw t
'TwoScans.TraceReadout.regular_detection' depends on axioms: [propext, Classical.choice, Quot.sound]
TwoScans.TraceSelect.readAt_sound {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [TwoScans.Automata.FinStates Q]
  [TwoScans.Automata.FinStates Γ] (δ : TwoScans.Tableau.OneTape.Table Q Γ) (blank : Γ)
  (c : TwoScans.Tableau.OneTape.Cfg Q Γ) (j n : ℕ) (row : List (TwoScans.Tableau.OneTape.Color Q Γ))
  (hit :
    TwoScans.TraceSelect.readAt δ blank n (TwoScans.Frames.rounds j (TwoScans.AnyTape.startTerm blank c)) =
      Option.some row) :
  ∃ (k : ℕ),
    row =
      TwoScans.Tableau.OneTape.encode
        (TwoScans.Tableau.OneTape.pad blank (TwoScans.Tableau.run (TwoScans.Tableau.OneTape.advance δ blank) c n) k)
'TwoScans.TraceSelect.readAt_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
TwoScans.TraceSelect.readAt_cofinal {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [TwoScans.Automata.FinStates Q]
  [TwoScans.Automata.FinStates Γ] (δ : TwoScans.Tableau.OneTape.Table Q Γ) (blank : Γ)
  (c : TwoScans.Tableau.OneTape.Cfg Q Γ) (horizon T : ℕ) :
  ∃ j > T,
    ∀ n ≤ horizon,
      ∃ (k : ℕ),
        TwoScans.TraceSelect.readAt δ blank n (TwoScans.Frames.rounds j (TwoScans.AnyTape.startTerm blank c)) =
          Option.some
            (TwoScans.Tableau.OneTape.encode
              (TwoScans.Tableau.OneTape.pad blank (TwoScans.Tableau.run (TwoScans.Tableau.OneTape.advance δ blank) c n)
                k))
'TwoScans.TraceSelect.readAt_cofinal' depends on axioms: [propext, Classical.choice, Quot.sound]
TwoScans.Chronology.trajectory {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [TwoScans.Automata.FinStates Q]
  [TwoScans.Automata.FinStates Γ] (δ : TwoScans.Tableau.OneTape.Table Q Γ) (blank : Γ)
  (c : TwoScans.Tableau.OneTape.Cfg Q Γ) :
  have e := TwoScans.Chronology.seed blank c;
  have row := fun (n : ℕ) =>
    TwoScans.Chronology.canonical blank
      (TwoScans.Tableau.OneTape.encode (TwoScans.Tableau.run (TwoScans.Tableau.OneTape.advance δ blank) c n));
  (∀ (j : ℕ) (t : TwoScans.Term) (n : ℕ) (y : List (TwoScans.Tableau.OneTape.Color Q Γ)),
      TwoScans.SerialTrace.At e j t → TwoScans.Chronology.reader δ blank t = Option.some (n, y) → y = row n) ∧
    ∃ (time : ℕ → ℕ),
      time 0 = 0 ∧
        (∀ (n : ℕ), time n < time (n + 1)) ∧
          ∀ (n : ℕ),
            ∃ (t : TwoScans.Term),
              TwoScans.SerialTrace.At e (time n) t ∧ TwoScans.Chronology.reader δ blank t = Option.some (n, row n)
'TwoScans.Chronology.trajectory' depends on axioms: [propext, Classical.choice, Quot.sound]
TwoScans.Chronology.linear_seed {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [TwoScans.Automata.FinStates Q]
  [TwoScans.Automata.FinStates Γ] (blank : Γ) :
  ∃ (a : ℕ) (b : ℕ),
    ∀ (c : TwoScans.Tableau.OneTape.Cfg Q Γ),
      TwoScans.size (TwoScans.Chronology.seed blank c) ≤ a + b * (c.left.length + 1 + c.right.length)
'TwoScans.Chronology.linear_seed' depends on axioms: [propext, Quot.sound]
TwoScans.Majority.universal_witness :
  ∃ (P : Type) (fp : TwoScans.Automata.FinStates P) (dp : DecidableEq P) (st : Inhabited P) (M :
    Turing.TM0.Machine TwoScans.UniversalS.Cell P) (a : ℕ) (b : ℕ),
    have E := TwoScans.Prize.encodeBits P;
    have D := TwoScans.Prize.readStrings M;
    have start := fun (p x : List Bool) => TwoScans.Majority.triple (E p x) (E p x) (E p x);
    (TwoScans.Automata.Regular fun (t : TwoScans.Term) =>
        ∃ (y : List Bool), TwoScans.Majority.read D t = Option.some y) ∧
      (∀ (p x : List Bool), TwoScans.size (start p x) ≤ a + b * (p.length + x.length)) ∧
        ∀ (f : List Bool →. List Bool),
          Partrec f →
            ∃ (p : List Bool),
              ∀ (x y : List Bool),
                (∃ (n : ℕ),
                    ∃ t ∈ TwoScans.SerialReadout.states (start p x) n, TwoScans.Majority.read D t = Option.some y) ↔
                  y ∈ f x
'TwoScans.Majority.universal_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source declarations in the same order:

- [`TwoScans.Certified.universality`](formal/Certified.lean#L12)
- [`TwoScans.Prize.serial_universal_witness`](formal/SerialOutput.lean#L11)
- [`TwoScans.OrbitHardness.concrete_indexed`](formal/OrbitHardness.lean#L25)
- [`TwoScans.TraceReadout.regular_detection`](formal/TraceReadout.lean#L264)
- [`TwoScans.TraceSelect.readAt_sound`](formal/TraceSelect.lean#L96)
- [`TwoScans.TraceSelect.readAt_cofinal`](formal/TraceSelect.lean#L110)
- [`TwoScans.Chronology.trajectory`](formal/Chronology.lean#L51)
- [`TwoScans.Chronology.linear_seed`](formal/Chronology.lean#L89)
- [`TwoScans.Majority.universal_witness`](formal/Majority.lean#L109)

</details>
