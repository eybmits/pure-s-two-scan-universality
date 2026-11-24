import ShellSelect

namespace TwoScans.Select
open Term Shell Automata

theorem select_origin {Q} (a : Fold (Q × Bool)) (yes : Q → Bool) (t : Term) (v)
    (h : select yes (decorate a t) = some v) :
    ∃ u, v = decorate a u ∧ Occ u t ∧ yes (a.run u).1 = true := by
  induction t with
  | s =>
    change (if yes (a.run s).1 then some (decorate a s) else none) = some v at h
    split at h
    · rename_i ok; cases h; exact ⟨_,rfl,.here,ok⟩
    · cases h
  | app l r il ir =>
    change (if yes (decorate a (app l r)).state.1 then some (decorate a (app l r)) else
      if (decorate a l).state.2 then select yes (decorate a l) else
      if (decorate a r).state.2 then select yes (decorate a r) else none) = some v at h
    rw [decoration_state] at h
    split at h
    · rename_i ok; cases h; exact ⟨_,rfl,.here,ok⟩
    · split at h
      · obtain ⟨u,e,o,hp⟩ := il h; exact ⟨u,e,.left o,hp⟩
      · split at h
        · obtain ⟨u,e,o,hp⟩ := ir h; exact ⟨u,e,.right o,hp⟩
        · cases h

/-- Called only at the selected shell. It consumes the immutable word spine,
    without recomputing either the static test or the scan. -/
def selectedRead {Y : Type} (value : List Bool → Y) : Term → Option Y
  | app (app _ p) _ => (readWord p).map value
  | _ => none

theorem selectedRead_eq {Y} (wp bp) (val : List Bool → Y) (t y)
    (ok : localReport wp bp val t = some y) : selectedRead val t = some y := by
  obtain ⟨w,r,rfl,_,_,rfl⟩ := (localReport_iff _ _ _ _ _).mp ok
  have rr := (readWord_iff _ w).2 rfl
  simp [selectedRead,tag,rr]

theorem select_without_retest {Y} (wp bp) (v : List Bool → Y)
    (row : Regular (fun t => ∃ w, t = W w ∧ wp w = true))
    (route : Regular (fun t => bp t = true)) :
    ∃ (Q : Type) (_ : FinStates Q) (a : Fold Q) (yes : Q → Bool), ∀ t,
       (select yes (decorate (marks a yes) t)).bind (fun node => selectedRead v node.erase)
         = first (localReport wp bp v) t := by
  obtain ⟨Q,iq,a,yes,correct⟩ := regular_local wp bp v row route
  refine ⟨Q,iq,a,yes,?_⟩
  intro t
  rw [←select_correct a yes (localReport wp bp v) correct]
  cases h : select yes (decorate (marks a yes) t) with
  | none => rfl
  | some n =>
    obtain ⟨u,rfl,_,ok⟩ := select_origin (marks a yes) yes t n h
    rw [show ((marks a yes).run u).1 = _ from Fold.extend_base ..] at ok
    obtain ⟨y,hy⟩ := (correct u).mp ok
    simp [selectedRead_eq wp bp v u y hy,hy]

#print axioms select_without_retest
end TwoScans.Select
