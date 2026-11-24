import OrbitReads
import WordBlocks

namespace TwoScans.NativeAlignment
open Term Frames Generation Shell Observer OrbitReads

def fast : List Bool → List Choice := List.map fun b => if b then .bFast else .a
def slowHead (n : Nat) : List Choice := List.replicate n .bSlow

theorem fast_letters (w : List Bool) : letters (fast w) = w := by
  induction w with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [fast,letters]

theorem fast_time (w : List Bool) : offset (fast w) = w.length := by
  induction w with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [fast,offset] <;> omega

theorem letters_append (p q : List Choice) : letters (p++q) = letters p ++ letters q := by
  induction p with
  | nil => rfl
  | cons c p ih => cases c <;> simp [letters,ih]

theorem offset_append (p q : List Choice) : offset (p++q) = offset p + offset q := by
  induction p with
  | nil => simp [offset]
  | cons c p ih => cases c <;> simp [offset,ih] <;> omega

theorem slow_letters (n) : letters (slowHead n) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [slowHead,List.replicate_succ,letters] using ih

theorem slow_time (n) : offset (slowHead n) = n+n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [slowHead,List.replicate_succ,offset] at *; omega

def path (delay : Bool) (bs : List Bool) (d : Nat) :=
  (if delay then slowHead d else fast (List.replicate d true)) ++ fast bs

theorem path_bits (delay bs d) : letters (path delay bs d) = List.replicate d true ++ bs := by
  cases delay <;> simp [path,letters_append,fast_letters,slow_letters]

theorem path_cost (delay bs d) : offset (path delay bs d) =
    d + bs.length + (if delay then d else 0) := by
  cases delay <;> simp [path,offset_append,fast_time,slow_time] <;> omega

/-- Two calibrated reads in any genuine shell at the *same* snapshot. The
second scanner's suffix is forced by the displacement, regardless of all
other activity in the tree. The empty suffix never counts as a read. -/
theorem calibrated_pair {i w pre0 pre1 tail1 terminal : List Bool}
    {n d age0 : Nat} {r : Term} (delay : Bool)
    (origin : Occ (tag w ⋆ r) (rounds n (seed i)))
    (secondProbe : w = List.replicate d true ++ pre1 ++ true :: tail1)
    (terminalShape : w = w.take age0 ++ terminal)
    (endPosition : age0 ≤ w.length)
    (start : probe (path false pre0 d) r = some (W terminal))
    (target : Nat) (clock : pre1.length + (if delay then d else 0) + target =
      pre0.length + age0) (inside : target < w.length) :
    probe (path delay pre1 d) r = some (W (w.drop target)) := by
  obtain ⟨_,age,_,rfl⟩ := (shell_orbit_iff i w r).mp ⟨n,origin⟩
  rw [local_eq] at start ⊢
  cases hs : bitRead w (path false pre0 d) age with
  | none => simp [hs] at start
  | some suffix =>
    have equal : suffix = terminal := word_injective (by simpa [hs] using start)
    obtain ⟨j,_,_,ha,hj,hz⟩ := read_position.mp hs
    have decoded : terminal = w.drop j := equal.symm.trans hz
    have l1 := congrArg List.length decoded
    have l2 := congrArg List.length terminalShape
    simp only [List.length_drop] at l1
    simp only [List.length_append,List.length_take,Nat.min_eq_left endPosition] at l2
    have same : j = age0 := by omega
    rw [path_cost] at ha
    have hb : bitRead w (path delay pre1 d) age = some (w.drop target) := by
      apply read_position.mpr
      refine ⟨target,tail1,?_,?_,inside,rfl⟩
      · simpa [path_bits,List.append_assoc] using secondProbe
      · rw [path_cost]; simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at ha; omega
    simp [hb]

end TwoScans.NativeAlignment
#print axioms TwoScans.NativeAlignment.calibrated_pair
