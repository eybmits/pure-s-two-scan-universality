import TraceReadout

namespace TwoScans.TraceSelect
open Tableau OneTape AnyTape Automata Shell Frames TraceReadout

/-- Split a symbol stream at row separators. The first component is the
    unfinished row, the second component holds rows after the first separator. -/
private def splitRows {X : Type} : List (Option X) → List X × List (List X)
  | [] => ([],[])
  | some c :: cs => let (r,rs) := splitRows cs; (c::r,rs)
  | none :: cs => let (r,rs) := splitRows cs; ([],r::rs)

private theorem split_prefix {X : Type} (r : List X) (tail : List (Option X)) :
    splitRows (r.map some ++ tail) = (r ++ (splitRows tail).1, (splitRows tail).2) := by
  induction r with
  | nil => simp
  | cons a r ih => simp [splitRows,ih]

private theorem split_pack {X : Type} (rs : List (List X)) : splitRows (pack rs) = ([],rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [pack,splitRows,split_prefix,ih]

/-- Preorder tie-breaking keeps the first list of maximal length. -/
private def longer {X : Type} (a b : List X) := if b.length ≤ a.length then a else b

private theorem longer_from {X : Type} (a b : List X) : longer a b = a ∨ longer a b = b := by
  unfold longer; split <;> simp_all

private theorem longer_bounds {X : Type} (a b : List X) :
    a.length ≤ (longer a b).length ∧ b.length ≤ (longer a b).length := by
  unfold longer; split <;> simp_all <;> omega

private def longest {X : Type} (read : Term → List X) : Term → List X
  | .s => read .s
  | .app l r => longer (read (.app l r)) (longer (longest read l) (longest read r))

private theorem longest_from {X : Type} (read : Term → List X) (t : Term) :
    ∃ u, Occ u t ∧ longest read t = read u := by
  induction t with
  | s => exact ⟨_,.here,rfl⟩
  | app l r il ir =>
    rcases longer_from (read (.app l r)) (longer (longest read l) (longest read r)) with root | child
    · exact ⟨_,.here,root⟩
    · rcases longer_from (longest read l) (longest read r) with left | right
      · obtain ⟨u,occ,eq⟩ := il; exact ⟨u,.left occ,child.trans (left.trans eq)⟩
      · obtain ⟨u,occ,eq⟩ := ir; exact ⟨u,.right occ,child.trans (right.trans eq)⟩

private theorem longest_bound {X : Type} (read : Term → List X) {u t} (occ : Occ u t) :
    (read u).length ≤ (longest read t).length := by
  induction occ with
  | here => cases u with
    | s => exact Nat.le_refl _
    | app l r => exact (longer_bounds ..).1
  | left h ih => exact Nat.le_trans ih (Nat.le_trans (longer_bounds ..).1 (longer_bounds ..).2)
  | right h ih => exact Nat.le_trans ih (Nat.le_trans (longer_bounds ..).2 (longer_bounds ..).2)

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [FinStates Q] [FinStates Γ]

private def prefixRows (blank : Γ) (w : List Bool) := (splitRows (readTrace (Q:=Q) blank w)).2

private def localRows (δ : Table Q Γ) (blank : Γ) (t : Term) :=
  (localReport (wordTest δ blank (fun _ => true)) (bodyTest (Q:=Q) (Γ:=Γ))
    (prefixRows (Q:=Q) blank) t).getD []

/-- Return the longest valid chronological prefix found anywhere in the
    snapshot, with the first in preorder selected on ties. Empty means no hit. -/
def readLongest (δ : Table Q Γ) (blank : Γ) (t : Term) := longest (localRows δ blank) t

theorem readLongest_sound (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) (j : Nat) :
    Correct δ blank c (readLongest δ blank (rounds j (startTerm blank c))) := by
  obtain ⟨u,occ,eq⟩ := longest_from (localRows δ blank) (rounds j (startTerm blank c))
  unfold readLongest; rw [eq]; unfold localRows
  cases hit : localReport (wordTest δ blank (fun _ => true)) (bodyTest (Q:=Q) (Γ:=Γ))
      (prefixRows (Q:=Q) blank) u with
  | none => intro i bound; simp at bound
  | some result =>
    obtain ⟨raw,r,rfl,wp,bp,rfl⟩ := (localReport_iff _ _ _ _ _).mp hit
    obtain ⟨rows,read,_,correct⟩ := read_sound δ blank (fun _ => true) c raw j ⟨r,occ,wp,bp⟩
    simpa only [Option.getD_some,prefixRows,read,split_pack] using correct

theorem readLongest_bound (δ : Table Q Γ) (blank : Γ) {t raw rows}
    (pass : Passing δ blank (fun _ => true) raw t) (read : readTrace (Q:=Q) blank raw = pack rows) :
    rows.length ≤ (readLongest δ blank t).length := by
  obtain ⟨r,occ,wp,bp⟩ := pass
  have out : prefixRows (Q:=Q) blank raw = rows := by rw [prefixRows,read,split_pack]
  have hit := (localReport_iff (wordTest δ blank (fun _ => true)) (bodyTest (Q:=Q) (Γ:=Γ))
    (prefixRows (Q:=Q) blank) (.app (tag raw) r) rows).mpr ⟨raw,r,rfl,wp,bp,out⟩
  have bound := longest_bound (localRows δ blank) occ
  simpa only [localRows,hit,Option.getD_some,readLongest] using bound

/-- Return the n-th configuration (including its finite blank padding), if a
    prefix covering that source index has been observed in this snapshot. -/
def readAt (δ : Table Q Γ) (blank : Γ) (n : Nat) (t : Term) := (readLongest δ blank t)[n]?

theorem readAt_sound (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) (j n : Nat) (row)
    (hit : readAt δ blank n (rounds j (startTerm blank c)) = some row) :
    ∃ k, row = encode (pad blank (run (advance δ blank) c n) k) := by
  unfold readAt at hit
  have bound : n < (readLongest δ blank (rounds j (startTerm blank c))).length := by
    by_cases h : n < (readLongest δ blank (rounds j (startTerm blank c))).length
    · exact h
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hit
      cases hit
  obtain ⟨k,eq⟩ := readLongest_sound δ blank c j n bound
  exact ⟨k,Option.some.inj (hit.symm.trans eq)⟩

/-- One deterministic snapshot readout covers an arbitrarily prescribed whole
    horizon after any time bound, also on nonhalting source runs. -/
theorem readAt_cofinal (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) (horizon T : Nat) :
    ∃ j > T, ∀ n ≤ horizon, ∃ k, readAt δ blank n (rounds j (startTerm blank c)) =
      some (encode (pad blank (run (advance δ blank) c n) k)) := by
  obtain ⟨j,raw,rows,late,pass,read,len,_⟩ := cofinal_prefix δ blank c horizon T
  refine ⟨j,late,?_⟩; intro n hi
  have bound := readLongest_bound δ blank pass read
  exact readLongest_sound δ blank c j n (by omega)

#print axioms readLongest_sound
#print axioms readLongest_bound
#print axioms readAt_sound
#print axioms readAt_cofinal
end TwoScans.TraceSelect
