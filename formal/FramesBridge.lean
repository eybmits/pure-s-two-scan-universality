import Frames

namespace TwoScans.Frames
open Term

theorem stepsLeft {a b} (r : Term) (h : Steps a b) : Steps (a ⋆ r) (b ⋆ r) := by
  induction h with
  | refl => exact .refl _
  | tail _ st ih => exact .tail ih (.left r st)

theorem stepsRight {a b} (l : Term) (h : Steps a b) : Steps (l ⋆ a) (l ⋆ b) := by
  induction h with
  | refl => exact .refl _
  | tail _ st ih => exact .tail ih (.right l st)

theorem stepsAppend {a b c} (h : Steps a b) (k : Steps b c) : Steps a c := by
  induction k with
  | refl => exact h
  | tail _ st ih => exact .tail ih st

/-- Every deterministic parallel round consists entirely of ordinary contextual S steps. -/
theorem piSteps (t : Term) : Steps t (pi t) := by
  induction t with
  | s => exact .refl _
  | app a b ha hb =>
    rw [pi]
    split
    · cases h : root a b with
      | none => exact .refl _
      | some u => exact .tail (.refl _) (root_sound h)
    · exact stepsAppend (stepsLeft b ha) (stepsRight (pi a) hb)

theorem roundsSteps (t : Term) (n : Nat) : Steps t (rounds n t) := by
  induction n generalizing t with
  | zero => exact .refl _
  | succ n ih => exact stepsAppend (piSteps t) (ih (pi t))

def slowCount : List Choice → Nat
  | [] => 0
  | .a::rest | .bFast::rest => slowCount rest
  | .bSlow::rest => 1 + slowCount rest

theorem offset_count (path : List Choice) :
    offset path = path.length + slowCount path := by
  induction path with
  | nil => rfl
  | cons c path ih =>
    cases c <;> simp only [offset,slowCount,List.length_cons,ih] <;> omega

#print axioms roundsSteps
#print axioms offset_count
end TwoScans.Frames
