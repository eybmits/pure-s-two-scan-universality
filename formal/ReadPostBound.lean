import UniversalS

namespace TwoScans.UniversalS
open Turing Automata FoldedTape Term Frames

variable {P : Type} [FinStates P] [DecidableEq P] [Inhabited P]

/-- The universal bit decoder emits at most two bits per node of any observed tree. -/
theorem readPost_length (M : TM0.Machine Cell P) (t : Term) (out : List Bool)
    (hit : readPost M t = some out) : out.length ≤ 2 * size t := by
  unfold readPost at hit
  obtain ⟨row, found, rfl⟩ := Option.map_eq_some_iff.mp hit
  have rowBound := AnyTape.report_length _ _ _ t row found
  have tapeBound := FoldedTape.rightOf_length row
  have digitBound : (TapeDecoder.digits (FoldedTape.rightOf row)).length ≤
      (FoldedTape.rightOf row).length := by
    unfold TapeDecoder.digits
    rw [List.length_reverse]
    exact List.length_filterMap_le _ _
  omega

#print axioms readPost_length

end TwoScans.UniversalS
