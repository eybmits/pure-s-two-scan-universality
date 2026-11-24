import Shell
import ObserverPacket

namespace TwoScans.OrbitReads
open Term Frames Generation Shell Observer

def probe (route : List Choice) (tree : Term) := (seek g route tree).bind (read g)

def bitRead (w : List Bool) (route : List Choice) (age : Nat) : Option (List Bool) :=
  if age < ready w then none else
    (ageAt route w (age-ready w)).bind fun j =>
      if j < w.length then some (w.drop j) else none

theorem local_eq (w route age) : probe route (body w age) = (bitRead w route age).map W := by
  have e := packet_probe tagger_nf (by decide : 3 ≤ size g) w route age
  change probe route (body w age) = _ at e
  rw [e]
  unfold bitRead
  split
  · rfl
  · cases ageAt route w (age - ready w) with
    | none => rfl
    | some j =>
      simp only [Option.bind_some]
      split <;> rfl

/-- An arbitrary number of actual readers in the same shell share one
and the same local age. Both directions quantify over the entire raw orbit. -/
theorem simultaneous (i w : List Bool) (requirements : (List Choice → Option Term) → Prop) :
    (∃ n r, Occ (tag w ⋆ r) (rounds n (seed i)) ∧ requirements (fun path => probe path r)) ↔
    ∃ extra age, w = extra ++ i ∧
      requirements (fun path => (bitRead w path age).map W) := by
  constructor
  · rintro ⟨n,r,o,h⟩
    obtain ⟨extra,age,he,hr⟩ := (shell_orbit_iff i w r).mp ⟨n,o⟩
    exact ⟨extra,age,he,by simpa only [hr,local_eq] using h⟩
  · rintro ⟨extra,age,he,h⟩
    obtain ⟨n,hn⟩ := (shell_orbit_iff i w (body w age)).mpr ⟨extra,age,he,rfl⟩
    exact ⟨n,body w age,hn,by simpa only [local_eq] using h⟩

theorem read_position {w path age suffix} : bitRead w path age = some suffix ↔
    ∃ j tail, w = letters path ++ true :: tail ∧
      age = ready w + offset path + 2 + j ∧ j < w.length ∧ suffix = w.drop j := by
  unfold bitRead
  by_cases he : age < ready w
  · simp only [ite_eq_left he, reduceCtorEq, false_iff]
    rintro ⟨j,tail,hw,ha,hj,hs⟩
    omega
  · simp only [ite_eq_right he,Option.bind_eq_some_iff]
    constructor
    · rintro ⟨j, found, e⟩
      obtain ⟨⟨tail, ht⟩, time⟩ := (ageAt_spec _ _ _ _).mp found
      split at e
      next hj => exact ⟨j,tail,ht,by omega,hj,(Option.some.inj e).symm⟩
      next => cases e
    · rintro ⟨j,tail,hw,ha,hj,hs⟩
      exact ⟨j,(ageAt_spec _ _ _ _).mpr ⟨⟨tail,hw⟩,by omega⟩,by simp [hj,hs]⟩

end TwoScans.OrbitReads
#print axioms TwoScans.OrbitReads.simultaneous
#print axioms TwoScans.OrbitReads.read_position
