import Certified
import OrbitHardness
import SerialOutput
import Chronology
import Majority
#check SerialTableau.parallel_agrees
#check SerialTableau.sweep_is_single_steps
#check TwoScans.SerialReadout.prefix_path
#check TwoScans.SerialReadout.one_is_step
#check TwoScans.Readback.first_preimage
#check TwoScans.Frames.B_delayed
#check TwoScans.Frames.scannerBirth
#check TwoScans.Scan.operandIdentity
#check TwoScans.Scan.noFalseScanAfterEnd
#check TwoScans.Observer.read_exact
#check TwoScans.Shell.shell_orbit_iff
#check TwoScans.Select.linear_selection
#check TwoScans.AnyTape.streamed_report
#check TwoScans.OrbitHardness.concrete_indexed
#check TwoScans.Join.checked_tests
#check TwoScans.Tableau.all_successors
#check TwoScans.WordRead.Attr
#check TwoScans.Automata.Regular
#check TwoScans.Frames.pi
#check TwoScans.Prize.serial_universal_witness
#check TwoScans.Majority.universal_witness
#check TwoScans.Generation.everyExtension

-- Each example checks the public theorem against an independently specified interface.
namespace SubmissionContracts
open TwoScans TwoScans.Automata TwoScans.Frames TwoScans.Prize TwoScans.SerialReadout
open SerialTableau TwoScans.UniversalS
set_option linter.style.haveILetI false
example :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
      (M : @Turing.TM0.Machine Cell P st) (a b : Nat), letI := fp; letI := dp; letI := st
      let E := encodeBits P
      let D := readStrings M
      let start := fun p x => pack (E p x) (E p x)
      Regular (fun t => ∃ y, double D t = some y) ∧
      (∀ q : List Bool → Bool, WordRead.Attr q →
        Regular (fun t => ∃ y, double D t = some y ∧ q y = true)) ∧
      (∀ p x, size (start p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n, readFirst (double D) (start p x) n = some y) ↔ y ∈ f x :=
  TwoScans.Prize.serial_universal_witness

open TwoScans.Majority in
example :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
      (M : @Turing.TM0.Machine Cell P st) (a b : Nat), letI := fp; letI := dp; letI := st
      let E := encodeBits P
      let D := readStrings M
      let start := fun p x => triple (E p x) (E p x) (E p x)
      Regular (fun t => ∃ y, read D t = some y) ∧
      (∀ p x, size (start p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n t, t ∈ states (start p x) n ∧ read D t = some y) ↔ y ∈ f x :=
  TwoScans.Majority.universal_witness


example :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
      (M : @Turing.TM0.Machine Cell P st), letI := fp; letI := dp; letI := st
      let O := fun t => ∃ y, readPost M t = some y
      let hit := fun cx : Code × Nat => ∃ n, O (rounds n (encodePost P cx.1 cx.2))
      Regular O ∧ REPred hit ∧ ¬ComputablePred hit ∧
      (∀ r : Nat → Prop, REPred r → ManyOneReducible r hit) ∧
      (∀ c x, hit (c,x) ↔ (c.eval x).Dom) :=
  TwoScans.OrbitHardness.concrete_indexed
end SubmissionContracts
