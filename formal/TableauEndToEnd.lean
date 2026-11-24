import TableauOrbit
import JoinGate
import ShellPayload
import OutputStream

/- This file discharges every interface field. Neither a universal source
machine nor any of its steps is an input to the detector during a reduction.
One fixed finite table specifies a fixed observer for all its inputs. -/
namespace TwoScans.Tableau.Certificate
open Automata OneTape MachineAlphabet Term Frames
variable {Q Z : Type} [DecidableEq Q] [DecidableEq Z] [FinStates Q] [FinStates Z]

def machineTests (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q) :
    Tests (alph Q Z) δ halt q where
  wordTest := Static.wordOK (alph Q Z) [] (rowsOK (stopped δ halt) halt q)
  bodyTest := Join.both (alph Q Z) Site.current Site.expected []
  decode := OutputStream.transduce (OutputStream.reader (alph Q Z) (fun | .finalCell c => valueCell c | _ => none)) .header
  wordSpec := Static.wordOK_iff (alph Q Z) [] (rowsOK (stopped δ halt) halt q)
  gateSpec := Join.both_iff (alph Q Z) (FiniteCodes.wide _) FiniteCodes.starts FiniteCodes.ends []
  decodeSpec us vs w _ := by
    rw [OutputStream.on_payload (alph Q Z) FiniteCodes.ends]
    unfold Static.outBits
    apply congrArg (fun f => us.filterMap f)
    funext t
    cases t <;> rfl
  regularWord := by
    apply Static.reg_wordOK
    exact ⟨Static.Phase (Cell Q Z) InputState, inferInstance, .tail false .empty,
      Static.advance (rule (stopped δ halt)) (haltCell halt) InputState.empty (inputStep q),
      Static.done inputAccept, fun _ => Iff.rfl⟩
  regularBody := Join.regular_both (alph Q Z) Site.current Site.expected []

/-- A regular fixed observer for the source program, on the entire domain
of finite ground S-trees (including malformed or off-orbit inputs). -/
theorem machine_regular (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q) :
    Regular (fun r => ∃ y, (machineTests δ halt q).report r = some y) :=
  (machineTests δ halt q).regular_report

/-- Every successful observation, at every round, is a correct source output. -/
theorem every_output (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q)
    (x y : List Bool) (n : Nat)
    (h : (machineTests δ halt q).report (rounds n (encodeInput (Z:=Z) q x)) = some y) :
    Computes δ halt q x y :=
  (machineTests δ halt q).sound x y n h

/-- From a raw ground S seed to the output of an arbitrary finite-state
one-tape machine on a semi-infinite tape, including empty input/output.
No calibration, input provenance, source simulation, or observer hypotheses. -/
theorem machine_output_iff (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q)
    (x y : List Bool) :
    (∃ n, (machineTests δ halt q).report (rounds n (encodeInput (Z:=Z) q x)) = some y) ↔
    Computes δ halt q x y :=
  (machineTests δ halt q).output_iff x y

/-- One fixed choice of seed encoder, detector and output function for
all inputs of a given finite machine, with an explicit linear tree-size
bound. The report returns none when no shell passes. -/
theorem machine_simulation (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q) :
    ∃ (e : List Bool → Term) (read : Term → Option (List Bool)) (a b : Nat),
      Regular (fun t => ∃ y, read t = some y) ∧
      (∀ x, size (e x) ≤ a + b*x.length) ∧
      ∀ x y, (∃ n, read (rounds n (e x)) = some y) ↔ Computes δ halt q x y := by
  let s := (alph Q Z).width
  refine ⟨encodeInput (Z:=Z) q, (machineTests δ halt q).report,
    2*size Shell.g + 1 + 3*(4*s), 3*s,machine_regular δ halt q,?_,machine_output_iff δ halt q⟩
  intro x
  have h := encoded_size (Z:=Z) q x
  change size (encodeInput (Z:=Z) q x) ≤ 2*size Shell.g + 1 + 3*((x.length+4)*s) at h
  simpa [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

#print axioms every_output
#print axioms machine_regular
#print axioms machine_output_iff
#print axioms machine_simulation
end TwoScans.Tableau.Certificate
