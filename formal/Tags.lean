import Anchors

namespace TwoScans
open Term

theorem Occ.appCases {a l r} (h : Occ a (app l r)) :
    a = app l r ∨ Occ a l ∨ Occ a r := by
  cases h with
  | here => exact .inl rfl
  | left o => exact .inr (.inl o)
  | right o => exact .inr (.inr o)

theorem Occ.sizeLE {a t} (h : Occ a t) : size a ≤ size t := by
  induction h with
  | here => exact Nat.le_refl _
  | left _ ih => simp [size]; omega
  | right _ ih => simp [size]; omega

/-- A dynamic application cannot shrink to the small tag prefix in one step. -/
theorem smallTarget {l v a b} (hl : Normal l) (hv : Normal v) (hs : Safe l v a)
    (st : Step a b) : size v < size b := by
  cases hs with
  | origL o => exact False.elim ((hl.sub o) _ st)
  | origR o => exact False.elim ((hv.sub o) _ st)
  | @join a r _ _ o =>
    have h1 := o.sizeLE
    have h2 := sizePos a
    have h3 := sizeStep st
    simp only [size] at h3
    omega

def NoRight (p t : Term) := ∀ a, ¬ Occ (app a p) t
def LeftOnly (p j t : Term) := ∀ a, Occ (app p a) t → a = j
def RightOnly (t p tree : Term) := ∀ a, Occ (app a t) tree → app a t = p

theorem noSmallRight {l v t p} (hs : Safe l v t) (small : size p < size v)
    (ol : NoRight p l) (ov : NoRight p v) : NoRight p t := by
  intro a o
  cases hs.sub o with
  | origL h => exact ol _ h
  | origR h => exact ov _ h
  | join _ _ h => have := h.sizeLE; omega

theorem onlySmallRight {l v t marker pre} (hs : Safe l v t) (small : size marker < size v)
    (ol : RightOnly marker pre l) (ov : RightOnly marker pre v) : RightOnly marker pre t := by
  intro a o
  cases hs.sub o with
  | origL h => exact ol _ h
  | origR h => exact ov _ h
  | join _ _ h => have := h.sizeLE; omega

/-- The isolated prefix P is never applied to a new handler. -/
theorem leftOnlyStep {l v t u p j}
    (hl : Normal l) (hv : Normal v) (hj : Normal j) (small : size p < size v)
    (st : Step t u) (hs : Safe l v t) (nr : NoRight p t) (old : LeftOnly p j t) :
    LeftOnly p j u := by
  induction st with
  | root x y z =>
    have anchored := Safe.cut hl hv hs (.root x y z)
    have hz := anchored.sizeLE
    intro a matchNew
    rcases matchNew.appCases with top | xz | yz
    · cases top
      simp only [size] at small
      omega
    · rcases xz.appCases with head | inX | inZ
      · cases head
        exact False.elim (nr s (.left (.left .here)))
      · exact old _ (.left (.left (.right inX)))
      · exact old _ (.right inZ)
    · rcases yz.appCases with head | inY | inZ
      · cases head
        exact False.elim (nr _ (.left .here))
      · exact old _ (.left (.right inY))
      · exact old _ (.right inZ)
  | left r st ih =>
    intro a o
    rcases o.appCases with top | ol | orr
    · cases top
      have := smallTarget hl hv hs.children.1 st
      omega
    · exact ih hs.children.1 (fun b x => nr b (.left x)) (fun b x => old b (.left x)) _ ol
    · exact old _ (.right orr)
  | right f st ih =>
    intro a o
    rcases o.appCases with top | ol | orr
    · cases top
      have eq := old _ .here
      rw [eq] at st
      exact False.elim (hj _ st)
    · exact old _ (.left ol)
    · exact ih hs.children.2 (fun b x => nr b (.right x)) (fun b x => old b (.right x)) _ orr

theorem leftOnlySteps {l v t u p j}
    (hl : Normal l) (hv : Normal v) (hj : Normal j) (small : size p < size v)
    (nl : NoRight p l) (nv : NoRight p v) (sts : Steps t u) (hs : Safe l v t)
    (old : LeftOnly p j t) : LeftOnly p j u := by
  induction sts with
  | refl => exact old
  | tail prev st ih =>
    have mid := keepsSafe hl hv hs prev
    exact leftOnlyStep hl hv hj small st mid (noSmallRight mid small nl nv) ih

/-- Neither of the two child applications in an S contraction can create
    a tag by any other choice of the redex's spine arguments. -/
theorem uniqueTagProducer {l v marker handler x y z}
    (hs : Safe l v (app (app (app s x) y) z))
    (small : size marker < size v)
    (ol : RightOnly marker (app s marker) l) (ov : RightOnly marker (app s marker) v)
    (prefixOK : LeftOnly (app s marker) handler (app (app (app s x) y) z))
    (birth : x = marker ∨ y = marker) : x = marker ∧ y = handler := by
  rcases birth with h | h
  · subst x
    exact ⟨rfl, prefixOK _ (.left .here)⟩
  · subst y
    have impossible := onlySmallRight hs small ol ov (app s x) (.left .here)
    cases impossible

#print axioms leftOnlySteps
#print axioms uniqueTagProducer
end TwoScans
