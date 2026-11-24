import FoldedRun

namespace TwoScans.FoldedTape
open Tableau.OneTape
variable {Q Γ Λ : Type}

def plain? : Color Q Γ → Option Γ
  | .plain a => some a
  | _ => none

/-- Find the head, remembering the cells before it in near-to-far order;
copy the symbols after the head. Every list node participates in one pass. -/
def parseRow (acc : List Γ) : List (Color Q Γ) → Option (Cfg Q Γ)
  | [] | .wall :: _ => none
  | .plain a :: rest => parseRow (a::acc) rest
  | .head q a :: rest => some ⟨acc,q,a,rest.filterMap plain?⟩

private theorem parse_prefix (p a : List Γ) (t : List (Color Q Γ)) :
    parseRow a (p.map .plain ++ t) = parseRow (p.reverse ++ a) t := by
  induction p generalizing a with
  | nil => rfl
  | cons c cs ih => simp [parseRow,ih,List.append_assoc]

theorem parses_encoded (c : Cfg Q Γ) : parseRow [] (encode c) = some c := by
  cases c with
  | mk l q a r =>
    simp [-List.map_reverse,encode,parse_prefix,parseRow,List.filterMap_append,List.filterMap_map,
      Function.comp_def,plain?]

/-- Return the inclusive right-hand Post tape. Both branches of readCfg
are concatenations, projections and reversals of sublists, hence linear
in the supplied finite row. Arbitrary suffix blanks have no effect. -/
def rightOf (row : List (Color (Control Λ) (Column Γ))) : List Γ :=
  match parseRow [] row with
  | none => []
  | some c => readCfg c

@[simp] theorem rightOf_encode (c : Cfg (Control Λ) (Column Γ)) :
    rightOf (encode c) = readCfg c := by rw [rightOf,parses_encoded]

theorem rightOf_padded [Inhabited Γ] [Inhabited Λ] (c : Cfg (Control Λ) (Column Γ)) (k : Nat) :
    Turing.ListBlank.mk (rightOf (encode (pad clear c k))) = Turing.ListBlank.mk (readCfg c) := by
  rw [rightOf_encode,pad_readCfg]

private theorem parse_size (p : List Γ) (r : List (Color Q Γ))
    (c : Cfg Q Γ) (h : parseRow p r = some c) :
    c.left.length + 1 + c.right.length ≤ p.length + r.length := by
  induction r generalizing p with
  | nil => cases h
  | cons t r ih =>
    cases t with
    | wall => cases h
    | plain a =>
      have k := ih (a::p) h
      simp only [List.length_cons] at k ⊢; omega
    | head q a =>
      obtain rfl := Option.some.inj h
      have h := List.length_filterMap_le (f := plain?) (l := r)
      simp only [List.length_cons]; omega

/-- The readout writes at most two tape symbols per supplied encoded site. -/
theorem rightOf_length (r : List (Color (Control Λ) (Column Γ))) :
    (rightOf r).length ≤ 2*r.length := by
  unfold rightOf
  cases h : parseRow [] r with
  | none => simp
  | some c =>
    have hs := parse_size [] r c h
    simp only [List.length_nil,Nat.zero_add] at hs
    rcases c with ⟨l,⟨q,s⟩,a,v⟩
    cases s <;> simp [readCfg,rightList,unpack] at * <;> omega

#print axioms rightOf_padded
end TwoScans.FoldedTape
