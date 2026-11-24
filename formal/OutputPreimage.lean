import UniversalS
import RowFinite
import ShellOutputPreimage

set_option linter.style.haveILetI false
namespace TwoScans.OutputPreimage
open Automata Tableau Tableau.OneTape FoldedTape UniversalS WordRead
open Turing

variable {P : Type} [FinStates P] [DecidableEq P] [Inhabited P]
local instance : DecidableEq UniversalPost.Cell := FiniteUniversalPost.cellDecEq

private theorem pull {α β γ : Type} (u : Term → Option α) (f : α → β) (g : β → γ)
    (p : γ → Bool) (h : Regular (fun t => ∃ r, u t = some r ∧ p (g (f r)) = true)) :
    Regular (fun t => ∃ y, ((u t).map f).map g = some y ∧ p y = true) := by
  obtain ⟨Q,i,a,yes,eq⟩ := h
  refine ⟨Q,i,a,yes,fun t => ?_⟩
  rw [eq]
  cases u t <;> simp

/-- A finite-state tree detector on the entire input term recognizes the
preimage of *each* regular output language for the actual string decoder. -/
theorem regular (M : TM0.Machine UniversalPost.Cell P) (test : List Bool → Bool)
    (recognizes : Attr test) : Regular (fun t =>
      ∃ y, (readPost M t).map List.dropLast = some y ∧ test y = true) := by
  obtain ⟨X,ix,x,s,out,h⟩ := recognizes
  letI := ix
  let testRow := fun r : RowFinite.Row P UniversalPost.Cell => test ((TapeDecoder.digits (rightOf r)).dropLast)
  have eTest : (fun w : RowFinite.Row P UniversalPost.Cell =>
      out (((TapeDecoder.digits (rightOf w)).dropLast).foldr s x)) = testRow :=
    funext (fun w => h _)
  have raw : Attr testRow := eTest ▸ RowFinite.read_attr (Λ:=P) s x out
  let halt := fun q : Control P => q.1.isNone
  exact pull (AnyTape.report (table M) clear halt) (fun r => TapeDecoder.digits (rightOf r))
    List.dropLast test (AnyTape.report_preimage (table M) clear halt testRow raw)

/-- A different finite tree automaton tests each requested output bit. -/
theorem regular_bit (M : TM0.Machine UniversalPost.Cell P) (i : Nat) (b : Bool) :
    Regular (fun t => ∃ y, (readPost M t).map List.dropLast = some y ∧ y[i]? = some b) := by
  simpa using regular M _ (WordRead.bit_attr i b)

theorem regular_value (M : TM0.Machine UniversalPost.Cell P) (y : List Bool) :
    Regular (fun t => (readPost M t).map List.dropLast = some y) := by
  simpa using regular M _ (WordRead.exact_attr y)

end TwoScans.OutputPreimage
#print axioms TwoScans.OutputPreimage.regular
#print axioms TwoScans.OutputPreimage.regular_bit
