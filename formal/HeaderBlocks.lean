import BlockWire

namespace TwoScans.HeaderBlocks
open WordBlocks TrackLayout

inductive Group (α : Type) where
  | data (a : α)
  | run
  | delimiter
  deriving DecidableEq

variable {α : Type}

def bits (A : Alphabet α) : Group α → List Bool
  | .data a => A.code a
  | .run => List.replicate A.width true
  | .delimiter => List.replicate (A.width-1) true ++ [false]

private theorem rep_succ (k : Nat) (b : Bool) :
    List.replicate (k+1) b = List.replicate k b ++ [b] := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (List.cons b) ih

def alphabet (A : Alphabet α) (wide : 1 < A.width)
    (begins : ∀ a, (A.code a).head? = some false) : Alphabet (Group α) where
  width := A.width
  positive := A.positive
  code := bits A
  length a := by cases a <;> simp [bits,A.length] <;> omega
  faithful x y eq := by
    obtain ⟨k,hk⟩ : ∃ k, A.width = k+2 := ⟨A.width-2,by omega⟩
    have heads (a : α) := begins a
    have headRun : (bits A (.run : Group α)).head? = some true := by simp [bits,hk,List.replicate_succ]
    have headDel : (bits A (.delimiter : Group α)).head? = some true := by simp [bits,hk,List.replicate_succ]
    have sep : bits A (.run : Group α) ≠ bits A .delimiter := by
      intro same
      change List.replicate A.width true = List.replicate (A.width-1) true ++ [false] at same
      rw [hk] at same
      change List.replicate ((k+1)+1) true = List.replicate (k+1) true ++ [false] at same
      rw [rep_succ (k+1)] at same
      simp at same
    cases x <;> cases y
    all_goals first | rfl | exact congrArg Group.data (A.faithful _ _ eq) |
      exact False.elim (sep eq) | exact False.elim (sep eq.symm) | skip
    all_goals have e := congrArg List.head? eq
    all_goals simp only [headRun,headDel,show ∀ a, (bits A (.data a)).head? = some false from heads] at e <;> cases e

def back (us : List U) (vs : List C) (w : Nat) : List (Group (Label U C)) :=
  (reverseBody us vs).map Group.data ++ [.delimiter] ++ List.replicate (w-1) .run

/-- Outside the body, every aligned block has a distinct header label. -/
def ungroup : Option (Group α) → Option α
  | some (.data a) => some a
  | _ => none

theorem back_read (us : List U) (vs : List C) (w j : Nat) :
    ungroup ((back us vs w)[j]?) = (reverseBody us vs)[j]? := by
  let z := reverseBody us vs
  change ungroup ((z.map Group.data ++ [.delimiter] ++ List.replicate (w-1) .run)[j]?) = z[j]?
  rw [List.append_assoc]
  simp only [List.getElem?_append,List.length_map]
  by_cases h : j < z.length
  · simp [h,ungroup]
  · simp only [ite_eq_right h, List.getElem?_eq_none (by omega : z.length ≤ j)]
    cases j - z.length with
    | zero => rfl
    | succ d =>
      simp [List.getElem?_replicate,ungroup]

theorem all_colors (us : List U) (vs : List C) (w j : Nat) :
    readColor (ungroup ((back us vs w)[j+1]?)) = vs[j]? := by
  rw [back_read,color_at]

end TwoScans.HeaderBlocks
#print axioms TwoScans.HeaderBlocks.all_colors
