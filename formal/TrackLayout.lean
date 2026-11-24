import WordBlocks

namespace TwoScans.TrackLayout
open WordBlocks

inductive Label (U C : Type) where
  | ub | ue | ve | vb
  | site (r : U)
  | color (c : C)
  deriving DecidableEq
open Label

variable {U C : Type}
def reverseBody (us : List U) (vs : List C) : List (Label U C) :=
  [vb] ++ vs.map color ++ [ve,ue] ++ us.reverse.map site ++ [ub]

def readColor : Option (Label U C) → Option C
  | some (.color c) => some c
  | _ => none

private theorem outside_colors (us : List U) (i : Nat) :
    readColor (([ve,ue] ++ us.reverse.map site ++ [ub] : List (Label U C))[i]?) = none := by
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
      by_cases h : i < us.reverse.length
      · simp only [List.getElem?_append, List.length_map, ite_eq_left h, List.getElem?_map, List.getElem?_eq_getElem h]; rfl
      · simp only [List.getElem?_append, List.length_map, ite_eq_right h]
        cases i - us.reverse.length <;> rfl

theorem color_at (us : List U) (vs : List C) (k : Nat) :
    readColor ((reverseBody us vs)[k+1]?) = vs[k]? := by
  simp only [reverseBody, List.cons_append, List.nil_append, List.getElem?_cons_succ,
    List.append_assoc]
  by_cases h : k < vs.length
  · simp [List.getElem?_append,h,readColor]
  · simp only [List.getElem?_append, List.length_map, ite_eq_right h]
    rw [List.getElem?_eq_none (by omega : vs.length ≤ k)]
    exact outside_colors us _

theorem end_unique (us : List U) (vs : List C) (j : Nat) :
    (reverseBody us vs)[j+1]? = some ve ↔ j = vs.length := by
  simp only [reverseBody, List.cons_append, List.nil_append, List.getElem?_cons_succ,
    List.append_assoc, List.getElem?_append, List.length_map]
  by_cases h : j < vs.length
  · simp [h]; omega
  · simp only [ite_eq_right h]
    generalize hd : j - vs.length = d
    cases d with
    | zero => simp; omega
    | succ d =>
      cases d with
      | zero => simp; omega
      | succ d =>
        simp only [List.getElem?_cons_succ, List.getElem?_append, List.length_map]
        by_cases he : d < us.reverse.length
        · simp only [ite_eq_left he, List.getElem?_map, List.getElem?_eq_getElem he, Option.map_some, Option.some.injEq]
          constructor
          · intro bad; cases bad
          · intro e; omega
        · simp only [ite_eq_right he]
          cases d - us.reverse.length <;> simp <;> omega

/-- Counting from the rear boundary turns the two reads into a mirror and
a shifted track. The endpoint and all site colors are read from the very same list. -/
theorem two_tracks {us : List U} {vs : List C} (current : U → C)
    (w : Nat) (finish : (reverseBody us vs)[us.length+1]? = some ve)
    (fast : ∀ i (h : i < us.length),
      readColor ((reverseBody us vs)[i+1]?) = some (current us[i])) :
    vs = us.map current ∧ ∀ i, readColor ((reverseBody us vs)[i+w+1]?) = (us.map current)[i+w]? := by
  have hlen := (end_unique us vs _).mp finish
  have same : vs = us.map current := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      have hh : i < us.length := by simpa using hj
      have got := fast i hh
      simpa [color_at,List.getElem?_eq_getElem hi] using got
  exact ⟨same,fun i => (color_at us vs _).trans (congrArg (fun l : List C => l[i+w]?) same)⟩

end TwoScans.TrackLayout
#print axioms TwoScans.TrackLayout.two_tracks
