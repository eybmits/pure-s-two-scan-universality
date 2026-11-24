import Frames

namespace TwoScans.Generation
open Term Frames

def Visible (t target : Term) := ∃ n, Occ target (rounds n t)

theorem Visible.now {t x} (h : Occ x t) : Visible t x := ⟨0, h⟩

theorem Visible.tick {t x} (h : Visible (pi t) x) : Visible t x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n+1, hn⟩

theorem rounds_fixed {v} (hv : nf v = true) (n) : rounds n v = v := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rounds, fixed hv] using ih

theorem Visible.left {v x} (h : Visible v x) (r) : Visible (v ⋆ r) x := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing v r with
  | zero => exact Visible.now (.left hn)
  | succ n ih =>
    cases h : nf v with
    | true => rw [rounds_fixed h] at hn; exact Visible.now (.left hn)
    | false =>
      apply Visible.tick
      simp only [pi,h,Bool.false_and,Bool.false_eq_true,ite_false]
      exact ih (pi r) hn

theorem Visible.right {v x} (h : Visible v x) (l) : Visible (l ⋆ v) x := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing v l with
  | zero => exact Visible.now (.right hn)
  | succ n ih =>
    cases h : nf v with
    | true => rw [rounds_fixed h] at hn; exact Visible.now (.right hn)
    | false =>
      apply Visible.tick
      simp only [pi,h,Bool.and_false,Bool.false_eq_true,ite_false]
      exact ih (pi l) hn

theorem Visible.context {v t x} (o : Occ v t) (h : Visible v x) : Visible t x := by
  induction o with
  | here => exact h
  | left _ ih => exact ih.left _
  | right _ ih => exact ih.right _

theorem Visible.after {n t x} (h : Visible (rounds n t) x) : Visible t x := by
  induction n generalizing t with
  | zero => exact h
  | succ n ih => exact (ih h).tick

theorem Visible.trans {a b c} (ab : Visible a b) (bc : Visible b c) : Visible a c := by
  obtain ⟨n, hn⟩ := ab
  exact Visible.after (Visible.context hn bc)

/-- Under any context, a strict left computation with a normal right operand
    reaches the application of its result to that operand. -/
theorem strictApp {n t u v} (h : Strict n t u) (hv : nf v = true) :
    rounds n (t ⋆ v) = u ⋆ v := by
  induction h with
  | zero => rfl
  | next hn _ ih =>
    simpa [rounds,pi,hn,fixed hv] using ih

theorem descend {g p x} (hg : nf g = true) (hp : nf p = true)
    (hx : nf x = true) (w : List Bool) :
    Visible (folded g p w ⋆ x) (g ⋆ x) := by
  induction w with
  | nil =>
    apply Visible.tick
    simp [folded,pi,root,nf,hg,hp,hx]
    exact Visible.now (.left .here)
  | cons letter tail ih =>
    have hn := folded_normal hg hp tail
    cases letter with
    | false =>
      apply Visible.tick
      rw [folded,A_extract hp hn hx]
      exact ih.right _
    | true =>
      apply Visible.tick
      rw [folded,B_direct hp hn hx]
      exact ih.left _

def op : Bool → Term | false => A | true => B
def renew (b : Bool) := s ⋆ (s ⋆ op b ⋆ s) ⋆ op b

theorem op_normal (b : Bool) : nf (op b) = true := by
  cases b <;> rfl

theorem renew_normal (b : Bool) : nf (renew b) = true := by
  cases b <;> rfl

theorem addWord (g : Term) (b : Bool) (w) : word g (b::w) = op b ⋆ word g w := by
  cases b <;> rfl

theorem renewal {g} (hg : nf g = true) (w : List Bool) (b : Bool) :
    Visible (renew b ⋆ word g w) (g ⋆ word g (b::w)) := by
  let p := word g w
  let x := word g (b::w)
  have hp : nf p = true := word_normal hg w
  have hx : nf x = true := word_normal hg (b::w)
  have pre : rounds 2 (renew b ⋆ p) = (x ⋆ (s ⋆ p)) ⋆ x := by
    cases b <;> simp [rounds,pi,root,nf,renew,op,A,B,x,p,word,word_normal hg w]
  apply Visible.after (n := 2)
  rw [pre]
  have run := strictApp (prepare hg hp (b::w)) hx
  apply Visible.after (n := cost (b::w))
  rw [show x = word g (b::w) from rfl, run]
  exact descend hg hp hx (b::w)

def gen (tagger guard : Term) :=
  s ⋆ renew false ⋆ (s ⋆ renew true ⋆ (s ⋆ tagger ⋆ guard))

theorem gen_normal {q u} (hq : nf q = true) (hu : nf u = true) :
    nf (gen q u) = true := by simp [gen,nf,root,renew_normal,hq,hu]

theorem forks {q u p} (hq : nf q = true) (hu : nf u = true) (hp : nf p = true) :
    Visible (gen q u ⋆ p) (q ⋆ p) ∧
    ∀ b, Visible (gen q u ⋆ p) (renew b ⋆ p) := by
  have first : pi (gen q u ⋆ p) = (renew false ⋆ p) ⋆ ((s ⋆ renew true ⋆ (s ⋆ q ⋆ u)) ⋆ p) := by
    simp [gen,pi,nf,root,hp,hq,hu,renew_normal]
  have second : pi ((s ⋆ renew true ⋆ (s ⋆ q ⋆ u)) ⋆ p) =
      (renew true ⋆ p) ⋆ ((s ⋆ q ⋆ u) ⋆ p) := by simp [pi,nf,root,hp,hq,hu,renew_normal]
  have third : pi ((s ⋆ q ⋆ u) ⋆ p) = (q ⋆ p) ⋆ (u ⋆ p) := by
    simp [pi,nf,root,hp,hq,hu]
  constructor
  · apply Visible.tick
    rw [first]
    apply Visible.right
    apply Visible.tick
    rw [second]
    apply Visible.right
    apply Visible.tick
    rw [third]
    exact Visible.now (.left .here)
  · intro b
    apply Visible.tick
    rw [first]
    cases b with
    | false => exact Visible.now (.left .here)
    | true =>
      apply Visible.right
      apply Visible.tick
      rw [second]
      exact Visible.now (.left .here)

/-- All left extensions of the initial suffix launch the actual tagger in
    the single maximal-parallel-innermost trajectory of the ground seed. -/
theorem everyExtension {q u} (hq : nf q = true) (hu : nf u = true)
    (initial extra : List Bool) :
    Visible (gen q u ⋆ word (gen q u) initial)
      (q ⋆ word (gen q u) (extra ++ initial)) := by
  have hg := gen_normal hq hu
  have grows (pre : List Bool) :
      Visible (gen q u ⋆ word (gen q u) initial)
        (gen q u ⋆ word (gen q u) (pre ++ initial)) := by
    induction pre with
    | nil => exact Visible.now .here
    | cons b tail ih =>
      have hp := word_normal hg (tail ++ initial)
      exact ih.trans (((forks hq hu hp).2 b).trans (renewal hg (tail ++ initial) b))
  exact (grows extra).trans (forks hq hu (word_normal hg _)).1

#print axioms everyExtension
end TwoScans.Generation
