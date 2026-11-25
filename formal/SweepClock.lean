import Shell
import Serial

/- A fixed ground term with arbitrarily wide serial sweeps. The proof uses
   only parallel innermost rounds and the live guard in the native generator. -/
namespace TwoScans.SweepClock
open Term Frames Generation Shell Live SerialTableau

private def width (t : Term) := (sweep t).length

private theorem root_empty {x y} (h : nf x = false ∨ nf y = false) :
    innermostRoot (app x y) = none := by
  cases q : innermostRoot (app x y) with
  | none => rfl
  | some v =>
    obtain ⟨_,hx,hy⟩ := innermostRoot_sound q
    have a := (nf_iff_normal x).mpr hx
    have b := (nf_iff_normal y).mpr hy
    rcases h with h|h <;> simp_all

private theorem width_app {x y} (h : nf x = false ∨ nf y = false) :
    width (app x y) = width x + width y := by
  simp [width,sweep,root_empty h]

private theorem width_pos {x} (h : nf x = false) : 0 < width x := by
  induction x with
  | s => simp [nf] at h
  | app a b iha ihb =>
    cases ga : nf a with
    | false => rw [width_app (Or.inl ga)]; have := iha ga; omega
    | true =>
      cases gb : nf b with
      | false => rw [width_app (Or.inr gb)]; have := ihb gb; omega
      | true =>
        cases er : Frames.root a b with
        | none => simp [nf,ga,gb,er] at h
        | some v => simp [width,sweep,innermostRoot,rootRule_agrees,normalB_agrees,ga,gb,er]

private theorem nf_super {a t} (o : Occ a t) (h : nf a = false) : nf t = false := by
  cases ht : nf t with
  | false => rfl
  | true => have hc := (nf_iff_normal _).mpr (((nf_iff_normal _).mp ht).sub o); simp_all

private theorem occurrence_step {a t} (o : Occ a t) (h : nf a = false) : Occ (pi a) (pi t) := by
  induction o with
  | here => exact .here
  | left o ih => simp only [pi,nf_super o h,Bool.false_and,Bool.false_eq_true,ite_false]; exact .left ih
  | right o ih => simp only [pi,nf_super o h,Bool.and_false,Bool.false_eq_true,ite_false]; exact .right ih

private theorem occurrence_width {a t} (o : Occ a t) (h : nf a = false) : width a ≤ width t := by
  induction o with
  | here => exact Nat.le_refl _
  | left o ih => rw [width_app (Or.inl (nf_super o h))]; omega
  | right o ih => rw [width_app (Or.inr (nf_super o h))]; omega

private theorem occurrence_rounds {a t} (o : Occ a t) (h : PiLive a) (n) :
    Occ (rounds n a) (rounds n t) := by
  induction n with
  | zero => exact o
  | succ n ih => rw [rounds_add n 1, rounds_add n 1]; exact occurrence_step ih (h n)

private def Wide (t : Term) (k : Nat) := ∃ T, ∀ n, T ≤ n → k ≤ width (rounds n t)

private theorem wide_visible {a b k} (visit : Visible a b) (live : PiLive b) (has : Wide b k) : Wide a k := by
  obtain ⟨j,occ⟩ := visit
  obtain ⟨start,lo⟩ := has
  refine ⟨j+start,?_⟩
  intro n hn
  have g := occurrence_width (occurrence_rounds occ live (n-j)) (live (n-j))
  rw [←rounds_add, Nat.add_sub_of_le (show j ≤ n by omega)] at g
  exact Nat.le_trans (lo (n-j) (by omega)) g

private theorem live_pair {r} (hl : PiLive r) (l n) :
    rounds n (app l r) = app (rounds n l) (rounds n r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rounds_add n 1,rounds_add n 1 l,rounds_add n 1 r,ih]
    change pi _ = app (pi _) (pi _)
    simp [pi,hl n]

/-- At every sufficiently late parallel round the standard serial sweep has
    at least k distinct native contractions. The initial clock is independent
    of k and of the program being observed. -/
theorem widening (k : Nat) (w : List Bool) : ∃ T, ∀ n, T ≤ n →
    k ≤ (SerialTableau.sweep (rounds n (seed w))).length := by
  change Wide (seed w) k
  induction k generalizing w with
  | zero => exact ⟨0,fun _ _ => Nat.zero_le _⟩
  | succ k ih =>
    let p := W w
    let r := (s ⋆ renew true ⋆ (s ⋆ tagger ⋆ U)) ⋆ p
    have hp : nf p = true := w_nf w
    have hu : nf U = true := by decide
    have a : pi (seed w) = (renew false ⋆ p) ⋆ r := by
      simp [seed,g,gen,r,p,pi,nf,root,w_nf,tagger_nf,hu,renew_normal]
    have rightVisit : Visible r (U ⋆ p) := by
      apply Visible.tick
      rw [show pi r = (renew true ⋆ p) ⋆ ((s ⋆ tagger ⋆ U) ⋆ p) by simp [r,pi,nf,root,hp,tagger_nf,hu,renew_normal]]
      apply Visible.right
      apply Visible.tick
      rw [show pi ((s ⋆ tagger ⋆ U) ⋆ p) = (tagger ⋆ p) ⋆ (U ⋆ p) by simp [pi,nf,root,hp,tagger_nf,hu]]
      exact Visible.now (.right .here)
    have rightLive := (Growing.ofVisible rightVisit (guardGrowth hp)).piLive
    have fresh : PiLive (seed (false::w)) := (genGrowth tagger_nf (w_nf _)).piLive
    obtain ⟨T,wider⟩ := wide_visible (renewal g_nf w false) fresh (ih (false::w))
    refine ⟨T+1,?_⟩
    intro n hn
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    change k+1 ≤ width (rounds j (pi (seed w)))
    rw [a,live_pair rightLive,width_app (Or.inr (rightLive j))]
    have lef : k ≤ width (rounds j (renew false ⋆ p)) := wider j (by omega)
    have rig := width_pos (rightLive j)
    omega

#print axioms widening
end TwoScans.SweepClock
