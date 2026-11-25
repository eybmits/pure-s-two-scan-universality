import MachineAlphabet
import ShellBlockLanguage
import ShellOutput
import SerialReadout

namespace TwoScans.InitialRowCode
open Automata WordBlocks Language Frames Shell SerialTableau

/-- Immutable literal data accompanying the two clocks and the dynamic seed. -/
def raw {α : Type} [FinStates α] [DecidableEq α] (xs : List α) : Term :=
  W (chunks (FiniteCodes.alphabet α) xs)

def decode (α : Type) [FinStates α] [DecidableEq α] (t : Term) : Option (List α) := do
  let w ← readWord t
  let a := FiniteCodes.alphabet α
  let (buf, xs) ← w.foldr (bitStep a List.cons) (some (cleanBuf a.width, []))
  if buf.val.isEmpty then some xs else none

@[simp] theorem decode_raw {α : Type} [FinStates α] [DecidableEq α] (xs : List α) :
    decode α (raw xs) = some xs := by
  unfold raw decode
  rw [(readWord_iff _ _).2 rfl]
  simp only [bind, Option.bind_some]
  rw [chunks_fold]
  simp [cleanBuf]

@[simp] theorem parallel_raw {α : Type} [FinStates α] [DecidableEq α] (xs : List α) :
    parallel (raw xs) = raw xs := by
  exact (parallel_agrees _).trans (fixed (w_nf _))

@[simp] theorem sweep_raw {α : Type} [FinStates α] [DecidableEq α] (xs : List α) :
    sweep (raw xs) = [] := by
  have h : Normal (raw xs) := (nf_iff_normal _).mp (w_nf _)
  have p := sweep_is_single_steps (raw xs)
  cases e : sweep (raw xs) with
  | nil => rfl
  | cons u us =>
    rw [e] at p
    cases p with
    | cons one _ => exact False.elim (h _ (SerialReadout.one_is_step one))

/-- Each source letter is represented by a fixed-width binary block. -/
theorem size_raw {α : Type} [FinStates α] [DecidableEq α] (xs : List α) :
    size (raw xs) ≤ size g + 1 + (3 * (FiniteCodes.alphabet α).width) * xs.length := by
  simpa [raw,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
    MachineAlphabet.word_bound (chunks (FiniteCodes.alphabet α) xs)

end TwoScans.InitialRowCode
#print axioms TwoScans.InitialRowCode.decode_raw
