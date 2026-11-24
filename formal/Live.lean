import Generation
import FramesBridge

namespace TwoScans.Live
open Term Frames Generation

def E := s ⋆ (s ⋆ A ⋆ A) ⋆ A
def L := s ⋆ (s ⋆ s ⋆ s) ⋆ s
def P := s ⋆ s ⋆ (s ⋆ E)
def U := s ⋆ (s ⋆ L) ⋆ P
def code (x : Term) := s ⋆ x ⋆ (s ⋆ E ⋆ x)
def numeral (g : Term) : Nat → Term
  | 0 => s ⋆ g
  | n+1 => A ⋆ numeral g n
def stack (g a : Term) : Nat → Term
  | 0 => s ⋆ g ⋆ a
  | n+1 => s ⋆ a ⋆ stack g a n

theorem numeral_nf {g} (hg : nf g = true) (n) : nf (numeral g n) = true := by
  induction n with
  | zero => simp [numeral,nf,root,hg]
  | succ n ih => simp [numeral,A,nf,root,ih]

theorem stack_nf {g a} (hg : nf g = true) (ha : nf a = true) (n) :
    nf (stack g a n) = true := by
  induction n with
  | zero => simp [stack,nf,root,hg,ha]
  | succ n ih => simp [stack,nf,root,ha,ih]

theorem prepA {g a} (hg : nf g = true) (ha : nf a = true) (n) :
    Strict n (numeral g n ⋆ a) (stack g a n) := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    apply Strict.next
    · simp [numeral,A,nf,root]
    · have h := ih.under (f:=s ⋆ a) (by simp [nf,root,ha])
      simpa [numeral,A,stack,pi,nf,root,ha,numeral_nf hg n] using h

theorem popA {g a x} (hg : nf g = true) (ha : nf a = true) (hx : nf x = true) (n) :
    Visible (stack g a n ⋆ x) (g ⋆ x) := by
  induction n with
  | zero =>
    apply Visible.tick
    simp [stack,pi,root,nf,hg,ha,hx]
    exact Visible.now (.left .here)
  | succ n ih =>
    apply Visible.tick
    simp [stack,pi,root,nf,stack_nf hg ha n,ha,hx]
    exact ih.right _

theorem diagonal {g} (hg : nf g = true) (n) :
    let a := numeral g n
    Visible ((a ⋆ a) ⋆ a) (g ⋆ a) := by
  let a := numeral g n
  have ha := numeral_nf hg n
  apply Visible.after (n:=n)
  rw [strictApp (prepA hg ha n) ha]
  exact popA hg ha ha n

theorem launch {x} (hx : nf x = true) :
    rounds 2 (L ⋆ x) = (((s ⋆ x) ⋆ (s ⋆ x)) ⋆ (s ⋆ x)) := by
  simp [rounds,pi,nf,root,L,hx]

theorem compiled {x} (hx : nf x = true) : nf (code x) = true := by
  simp [code,nf,root,hx,E,A]

theorem boot {x} (hx : nf x = true) : Visible (U ⋆ x) (code x ⋆ numeral (code x) 0) := by
  have h3 : rounds 3 (U ⋆ x) = (L ⋆ code x) ⋆ (x ⋆ code x) := by
    simp [rounds,pi,nf,root,U,P,L,E,A,code,hx]
  apply Visible.after (n:=3)
  rw [h3]
  apply Visible.left
  apply Visible.after (n:=2)
  rw [launch (compiled hx)]
  exact diagonal (compiled hx) 0

theorem restart {x} (hx : nf x = true) (n : Nat) :
    Visible (code x ⋆ numeral (code x) n) (code x ⋆ numeral (code x) (n+1)) := by
  let a := numeral (code x) n
  have ha : nf a = true := numeral_nf (compiled hx) n
  have f1 : pi (code x ⋆ a) = (x ⋆ a) ⋆ ((s ⋆ E ⋆ x) ⋆ a) := by
    simp [code,pi,nf,root,E,A,hx,ha]
  have f2 : pi ((s ⋆ E ⋆ x) ⋆ a) = (E ⋆ a) ⋆ (x ⋆ a) := by
    simp [pi,nf,root,E,A,hx,ha]
  have e2 : rounds 2 (E ⋆ a) = ((A ⋆ a) ⋆ (A ⋆ a)) ⋆ (A ⋆ a) := by
    simp [rounds,pi,nf,root,E,A,ha]
  apply Visible.tick
  rw [f1]
  apply Visible.right
  apply Visible.tick
  rw [f2]
  apply Visible.left
  apply Visible.after (n:=2)
  rw [e2]
  exact diagonal (compiled hx) (n+1)

def Growing (t : Term) := ∀ k : Nat, ∃ a, Visible t a ∧ k ≤ size a

theorem Growing.ofVisible {a b} (h : Visible a b) (g : Growing b) : Growing a := by
  intro k
  obtain ⟨v,hv,hs⟩ := g k
  exact ⟨v,h.trans hv,hs⟩

theorem guardGrowth {x} (hx : nf x = true) : Growing (U ⋆ x) := by
  intro k
  have reachable (n) : Visible (U ⋆ x) (code x ⋆ numeral (code x) n) := by
    induction n with
    | zero => exact boot hx
    | succ n ih => exact ih.trans (restart hx n)
  have large (n) : n ≤ size (numeral (code x) n) := by
    induction n with
    | zero => omega
    | succ n ih => simp [numeral,size,A]; omega
  exact ⟨_,reachable k, by simp only [size]; have h := large k; omega⟩

theorem subsize {a t} (h : Occ a t) : size a ≤ size t := by
  induction h with
  | here => exact Nat.le_refl _
  | left _ ih => simp only [size]; omega
  | right _ ih => simp only [size]; omega

theorem stepSizes {a t} (h : Steps a t) : size a ≤ size t := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ st ih => exact Nat.le_trans ih (sizeStep st)

def PiLive (t : Term) := ∀ n, nf (rounds n t) = false

theorem Growing.piLive {t} (g : Growing t) : PiLive t := by
  intro n
  cases h : nf (rounds n t) with
  | false => rfl
  | true =>
    obtain ⟨a,⟨m,occ⟩,huge⟩ := g (size (rounds n t)+1)
    have inM := subsize occ
    by_cases le : m ≤ n
    · have mono := stepSizes (roundsSteps (rounds m t) (n-m))
      rw [← Frames.rounds_add, Nat.add_sub_of_le le] at mono
      omega
    · have le' : n ≤ m := by omega
      have eqn := Frames.rounds_fixed h (m-n)
      rw [← Frames.rounds_add, Nat.add_sub_of_le le'] at eqn
      rw [eqn] at inM
      omega

theorem guardLive {x} (hx : nf x = true) : PiLive (U ⋆ x) := (guardGrowth hx).piLive

theorem genGrowth {tag x} (hq : nf tag = true) (hx : nf x = true) :
    Growing (gen tag U ⋆ x) := by
  have hu : nf U = true := by decide
  apply Growing.ofVisible (b:=U ⋆ x) _ (guardGrowth hx)
  have f1 : pi (gen tag U ⋆ x) =
      (renew false ⋆ x) ⋆ ((s ⋆ renew true ⋆ (s ⋆ tag ⋆ U)) ⋆ x) := by
    simp [gen,pi,nf,root,hq,hu,hx,renew_normal]
  have f2 : pi ((s ⋆ renew true ⋆ (s ⋆ tag ⋆ U)) ⋆ x) =
      (renew true ⋆ x) ⋆ ((s ⋆ tag ⋆ U) ⋆ x) := by
    simp [pi,nf,root,hq,hu,hx,renew_normal]
  apply Visible.tick
  rw [f1]
  apply Visible.right
  apply Visible.tick
  rw [f2]
  apply Visible.right
  apply Visible.tick
  simp [pi,nf,root,hq,hu,hx]
  exact Visible.now (.right .here)

theorem taggedLaunchLive {tag} (hq : nf tag = true) (w : List Bool) :
    PiLive (L ⋆ word (gen tag U) w) := by
  let g := gen tag U
  let p := word g w
  let q := s ⋆ p
  let v := q ⋆ q
  have hg : nf g = true := gen_normal hq (by decide)
  have hp : nf p = true := word_normal hg w
  have hq' : nf q = true := by simp [q,nf,root,hp]
  have hv : nf v = true := by simp [v,q,nf,root,hp]
  apply Growing.piLive
  apply Growing.ofVisible (b:=g ⋆ v) _ (genGrowth hq hv)
  apply Visible.after (n:=2)
  rw [launch hp]
  apply Visible.tick
  have one : pi ((q ⋆ q) ⋆ q) = (p ⋆ q) ⋆ v := by
    simp [q,v,pi,nf,root,hp]
  rw [show ((s ⋆ word (gen tag U) w) ⋆ (s ⋆ word (gen tag U) w)) ⋆ (s ⋆ word (gen tag U) w) = (q ⋆ q) ⋆ q from rfl,one]
  apply Visible.after (n:=cost w)
  rw [show p = word g w from rfl, show q = s ⋆ p from rfl, strictApp (prepare hg hp w) hv]
  exact descend hg hp hv w

#print axioms guardLive
#print axioms taggedLaunchLive
end TwoScans.Live
