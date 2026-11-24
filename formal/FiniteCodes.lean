import PayloadBits
import ShellAutomata
import TableauTracks

namespace TwoScans.FiniteCodes
open Automata WordBlocks

/-- A transparent constructive choice of fixed-width code for any explicitly
finite alphabet. The first/last bits are the common start and probe bits. -/
def code [DecidableEq α] [FinStates α] (a : α) : List Bool :=
  [false] ++ (FinStates.enum (Q := α)).map (fun x => decide (x = a)) ++ [true]

def alphabet (α : Type) [DecidableEq α] [FinStates α] : Alphabet α where
  width := (FinStates.enum (Q := α)).length + 2
  positive := by omega
  code := code
  length a := by simp [code]
  faithful a b h := by
    have hs : (FinStates.enum (Q := α)).map (fun x => decide (x = a)) =
      FinStates.enum.map (fun x => decide (x = b)) := by simpa [code] using h
    have m := List.map_inj_left.mp hs a (FinStates.covers a)
    simpa using m

theorem wide (α : Type) [DecidableEq α] [FinStates α] : 1 < (alphabet α).width := by
  change 1 < (FinStates.enum (Q := α)).length + 2; omega
theorem starts {α : Type} [DecidableEq α] [FinStates α] (a : α) :
    ((alphabet α).code a).head? = some false := rfl
theorem ends {α : Type} [DecidableEq α] [FinStates α] (a : α) :
    ∃ b, (alphabet α).code a = b ++ [true] := ⟨_,rfl⟩

end TwoScans.FiniteCodes
#print axioms TwoScans.FiniteCodes.alphabet
