import ObserverRoute

namespace TwoScans.Observer
open Term Frames Scan Generation Live

/-- The raw route encounters a B probe exactly at a matching position that
    has been split for sufficiently many rounds. -/
theorem ageAt_spec (path w t j) :
    ageAt path w t = some j ↔
    (∃ tail, w = letters path ++ true::tail) ∧ t = offset path + 2 + j := by
  induction path generalizing w t j with
  | nil =>
    cases w with
    | nil => simp [ageAt,letters,offset]
    | cons b w =>
      cases b <;> cases t with
      | zero => simp [ageAt,letters,offset] <;> omega
      | succ t =>
        cases t <;> simp [ageAt,letters,offset] <;> omega
  | cons c cs ih =>
    cases w with
    | nil => cases c <;> simp [ageAt,letters,offset]
    | cons b w =>
      cases c <;> cases b <;> cases t with
      | zero => simp [ageAt,letters,offset] <;> omega
      | succ t =>
        cases t <;> simp [ageAt,letters,offset,ih,List.cons_append] <;>
          omega

private theorem prefixRounds {n a b} (h : Strict n a b) {v} (hv : nf v = true)
    (i) (le : i ≤ n) : rounds i (a ⋆ v) = rounds i a ⋆ v := by
  induction h generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | next ha _ ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [rounds,pi,ha,fixed hv] using ih i (by omega)

def ready (w : List Bool) := 3 + cost w

private theorem startup {g} (hg : nf g = true) (w) :
    let p := word g w
    rounds 3 (L ⋆ p) = (p ⋆ (s ⋆ p)) ⋆ probeV g w := by
  let p := word g w
  have hp := word_normal hg w
  change pi (rounds 2 (L ⋆ p)) = _
  rw [launch hp]
  simp [pi,nf,root,hp,probeV,operand]

theorem becomeBranch {g} (hg : nf g = true) (w) :
    rounds (ready w) (L ⋆ word g w) = branch g w w := by
  rw [ready,Frames.rounds_add,startup hg,strictApp (prepare hg (word_normal hg _) w) (probe_normal hg w)]
  rfl

theorem slot_before {g} (hg : nf g = true) (w) (i) (early : i < ready w) :
    slot g (rounds i (L ⋆ word g w)) = none := by
  have hp := word_normal hg w
  cases i with
  | zero => simp [rounds,slot,hp]
  | succ i =>
    cases i with
    | zero => simp [rounds,pi,L,slot,nf,root,hp]
    | succ i =>
      cases i with
      | zero => rw [launch hp]; simp [slot, nf,root,hp]
      | succ i =>
        have hi : i ≤ cost w := by unfold ready at early; omega
        rw [show i+1+1+1 = 3+i by omega,Frames.rounds_add,startup hg]
        rw [prefixRounds (prepare hg hp w) (probe_normal hg w) i hi]
        simp [slot,probe_normal hg]

theorem seek_none {g t} (h : slot g t = none) (path) : seek g path t = none := by
  cases path with
  | nil => simp [seek,h]
  | cons c cs => cases c <;> simp [seek,h]

/-- All ages are measured from the birth of the original raw L packet.
    No early preparation state can produce a successful read. -/
theorem packet_probe {tag} (ht : nf tag = true) (big : 3 ≤ size (gen tag U))
    (w path t) :
    let g := gen tag U
    (seek g path (rounds t (L ⋆ word g w))).bind (read g) =
      if t < ready w then none else
        (ageAt path w (t - ready w)).bind (fun j =>
          if j < w.length then some (word g (w.drop j)) else none) := by
  let g := gen tag U
  have hg : nf g = true := gen_normal ht (by decide)
  dsimp only
  split
  next early => rw [seek_none (slot_before hg w t early)]; rfl
  next late =>
    have parts : ready w + (t - ready w) = t := by omega
    have eq : rounds t (L ⋆ word g w) = rounds (t - ready w) (branch g w w) := by
      calc
        _ = rounds (ready w + (t - ready w)) (L ⋆ word g w) := congrArg (fun n => rounds n _) parts.symm
        _ = _ := by rw [Frames.rounds_add,becomeBranch hg]
    rw [eq]
    exact probe_observation ht big w path w _

#print axioms ageAt_spec
#print axioms packet_probe
end TwoScans.Observer
