import Shell
import ShellWordAutomata

namespace TwoScans.Shell
open Term Frames Generation Automata

/-- Copy the payload word by a deterministic walk down its right spine. A
    constant comparison at each node identifies its wrapper. -/
def readWord := wordValue g ([] : List Bool) List.cons

theorem readWord_iff (t w) : readWord t = some w ↔ t = W w := by
  have fold_id (u : List Bool) : u.foldr List.cons [] = u := by
    induction u with | nil => rfl | cons a u ih => simp [ih]
  change wordValue _ _ _ _ = _ ↔ _
  rw [wordValue_some]
  simp only [fold_id]
  constructor
  · rintro ⟨v,rfl,rfl⟩; rfl
  · intro h; exact ⟨w,h,rfl⟩

/-- The root test and the immutable-word readout; the body test examines only
    the right child of this shell. -/
def localReport {Y : Type} (wordOK : List Bool → Bool) (bodyOK : Term → Bool)
    (value : List Bool → Y) (t : Term) : Option Y :=
  match t with
  | .app (.app m p) r =>
    if m = marker then
      (readWord p).bind (fun w => if wordOK w && bodyOK r then some (value w) else none)
    else none
  | _ => none

theorem localReport_iff {Y} (wp bp) (v : List Bool → Y) (t y) :
    localReport wp bp v t = some y ↔
      ∃ w r, t = tag w ⋆ r ∧ wp w = true ∧ bp r = true ∧ v w = y := by
  cases t with
  | s => simp [localReport]
  | app l r =>
    cases l with
    | s => simp [localReport,tag]
    | app m p =>
      constructor
      · intro h
        simp only [localReport] at h
        split at h
        · rename_i hm; subst m
          cases e : readWord p with
          | none => simp [e] at h
          | some w =>
            have pe := (readWord_iff p w).mp e
            simp only [e,Option.bind_some] at h
            split at h
            · rename_i ok; have pair : wp w = true ∧ bp r = true := by simpa using ok
              exact ⟨w,r,by rw [pe]; rfl,pair.1,pair.2,Option.some.inj h⟩
            · cases h
        · cases h
      · rintro ⟨w,r',eq,hp,hb,hv⟩
        obtain ⟨mt,rt⟩ := Term.app.inj eq
        obtain ⟨me,pe⟩ := Term.app.inj mt
        have read := (readWord_iff _ _).mpr pe
        simp [localReport,me,read,hp,rt,hb,hv]

/-- The first locally successful shell in preorder. -/
def first {Y : Type} (read : Term → Option Y) : Term → Option Y
  | s => read s
  | .app l r => (read (.app l r)).or ((first read l).or (first read r))

theorem first_sound {Y : Type} (read : Term → Option Y) (t y) (hit : first read t = some y) :
    ∃ u, Occ u t ∧ read u = some y := by
  induction t with
  | s => exact ⟨s,.here,hit⟩
  | app l r il ir =>
    simp only [first] at hit
    cases root : read (.app l r) with
    | some z =>
      simp [root] at hit
      exact ⟨_,.here,root.trans (congrArg some hit)⟩
    | none =>
      cases lc : first read l with
      | some z =>
        simp [root,lc] at hit
        obtain ⟨u,o,ok⟩ := il (lc.trans (congrArg some hit))
        exact ⟨_,.left o,ok⟩
      | none =>
        simp [root,lc] at hit
        obtain ⟨u,o,ok⟩ := ir hit
        exact ⟨_,.right o,ok⟩

theorem first_success {Y : Type} (read : Term → Option Y) {u t} (o : Occ u t) {y}
    (hit : read u = some y) : ∃ z, first read t = some z := by
  induction o with
  | @here =>
    cases u with
    | s => exact ⟨_,hit⟩
    | app l r => exact ⟨y,by simp [first,hit]⟩
  | @left l r o ih =>
    obtain ⟨z,ih⟩ := ih
    cases e : read (.app l r) <;> simp [first,e,ih]
  | @right l r o ih =>
    obtain ⟨z,ih⟩ := ih
    cases e : read (.app l r) <;> cases f : first read l <;> simp [first,e,f,ih]

/-- Every output of the actual preorder decoder on an actual snapshot is the
    readout from a generated extension at an actual local packet age. -/
theorem first_output_sound {Y} (wp bp) (v : List Bool → Y) (i n y)
    (h : first (localReport wp bp v) (rounds n (seed i)) = some y) :
    ∃ extra age, wp (extra ++ i) = true ∧ bp (body (extra ++ i) age) = true ∧ v (extra ++ i) = y := by
  obtain ⟨t,o,h⟩ := first_sound _ _ _ h
  obtain ⟨w,r,rfl,hw,hr,hv⟩ := (localReport_iff _ _ _ _ _).1 h
  obtain ⟨extra,age,rfl,rfl⟩ := (shell_orbit_iff i w r).1 ⟨n,o⟩
  exact ⟨extra,age,hw,hr,hv⟩

theorem first_output_domain {Y} (wp bp) (v : List Bool → Y) (i) :
    (∃ n y, first (localReport wp bp v) (rounds n (seed i)) = some y) ↔
      ∃ extra age, wp (extra ++ i) = true ∧ bp (body (extra ++ i) age) = true := by
  constructor
  · rintro ⟨n,y,h⟩
    obtain ⟨e,j,hw,hr,_⟩ := first_output_sound _ _ _ _ _ _ h
    exact ⟨e,j,hw,hr⟩
  · rintro ⟨e,j,hw,hr⟩
    obtain ⟨n,o⟩ := shell_visible i e j
    have hit := (localReport_iff wp bp v (shell (e ++ i) j) _).mpr ⟨_,_,rfl,hw,hr,rfl⟩
    exact ⟨n,first_success _ o hit⟩

/-- A regular payload test and a regular body test induce a regular hit test
    on arbitrary ground terms, including trees outside every generated orbit. -/
theorem regular_first {Y} (wp bp) (v : List Bool → Y)
    (rwrd : Regular (fun t => ∃ w, t = W w ∧ wp w = true))
    (rbdy : Regular (fun r => bp r = true)) :
    Regular (fun t => ∃ y, first (localReport wp bp v) t = some y) := by
  obtain ⟨Q,iq,a,p,h⟩ := regular_somewhere (regular_app (regular_app (regular_exact marker) rwrd) rbdy)
  refine ⟨Q,iq,a,p,?_⟩
  intro t; rw [h]
  constructor
  · rintro ⟨u,o,l,r,rfl,⟨m,word,rfl,rfl,w,rfl,hw⟩,hr⟩
    exact first_success _ o ((localReport_iff _ _ _ _ _).2 ⟨w,r,rfl,hw,hr,rfl⟩)
  · rintro ⟨y,hit⟩
    obtain ⟨u,o,hu⟩ := first_sound _ _ _ hit
    obtain ⟨w,r,rfl,hw,hr,_⟩ := (localReport_iff _ _ _ _ _).1 hu
    exact ⟨_,o,_,_,rfl,⟨_,_,rfl,rfl,w,rfl,hw⟩,hr⟩

#print axioms first_output_sound
#print axioms first_output_domain
#print axioms regular_first
end TwoScans.Shell
