import TrackLayout
import NativeAlignment

namespace TwoScans.BlockWire
open Term Frames Shell OrbitReads NativeAlignment WordBlocks TrackLayout

/-- Reverse block number 0 denotes the terminal boundary. Earlier blocks in
the written word have increasing reverse indices. The header sits before them. -/
def wire (A : Alphabet α) (head footer : List Bool) (back : List α) :=
  head ++ chunks A back.reverse ++ footer

theorem length_wire (A : Alphabet α) (head footer : List Bool) (back : List α) :
    (wire A head footer back).length = head.length + back.length*A.width + footer.length := by
  simp [wire,Nat.add_assoc]

theorem located {A : Alphabet α} {head foot : List Bool} {left right : List α} {a : α} :
    let w := wire A head foot (left ++ a :: right)
    (w.drop (head.length + right.length * A.width)).take A.width = A.code a := by
  dsimp only [wire]
  have e : (left ++ a::right).reverse = right.reverse ++ a::left.reverse := by simp
  rw [e]
  simpa only [List.length_reverse] using split_read A head right.reverse a left.reverse foot

theorem at_index {A : Alphabet α} (head foot : List Bool) (back : List α)
    (j : Nat) (hj : j < back.length) :
    (((wire A head foot back).drop (head.length + (back.length-1-j)*A.width)).take A.width)
      = A.code back[j] := by
  let right := back.drop (j+1)
  have hs : back = back.take j ++ back[j] :: right := by
    exact (List.take_append_drop j back).symm.trans (congrArg (back.take j ++ ·) (List.drop_eq_getElem_cons hj))
  have hh : right.length = back.length-1-j := by simp [right]; omega
  rw [← hh]
  calc
    _ = (((wire A head foot (back.take j ++ back[j] :: right)).drop _).take A.width) := congrArg (fun l => ((wire A head foot l).drop _).take A.width) hs
    _ = _ := located

/-- A hit on the exact V-boundary suffix calibrates *actual raw probes*. An
aligned subsequent probe reads precisely the indicated rear-numbered block. -/
theorem raw_code {A : Alphabet α} {head foot : List Bool} {back : List α}
    {i pre0 pre1 tail : List Bool} {n d : Nat} {r : Term}
    (j : Nat) (hj : j < back.length) (delay : Bool)
    (w : List Bool) (hw : w = wire A head foot back)
    (o : Occ (tag w ⋆ r) (rounds n (seed i)))
    (p1 : w = List.replicate d true ++ pre1 ++ true :: tail)
    (start : probe (path false pre0 d) r =
      some (W (w.drop (head.length + (back.length-1)*A.width))))
    (timing : pre1.length + (if delay then d else 0) = pre0.length + j*A.width) :
    ∃ suffix, probe (path delay pre1 d) r = some (W suffix) ∧
      suffix.take A.width = A.code back[j] := by
  let b := head.length + (back.length-1)*A.width
  let target := head.length + (back.length-1-j)*A.width
  have cutoff : b ≤ w.length := by
    rw [hw,length_wire]
    have hmul := Nat.mul_le_mul_right A.width (show back.length-1 ≤ back.length by omega)
    unfold b
    omega
  have hj' : back.length-1-j + j = back.length-1 := by omega
  have clock : pre1.length + (if delay then d else 0) + target = pre0.length + b := by
    have hi := congrArg (· * A.width) hj'
    simp only [Nat.add_mul] at hi
    unfold b target
    omega
  have hi : target < w.length := by
    rw [hw,length_wire]
    have hm := Nat.mul_lt_mul_of_pos_right (show back.length-1-j < back.length by omega) A.positive
    unfold target
    omega
  exact ⟨w.drop target, calibrated_pair delay o p1 (List.take_append_drop b w).symm
    cutoff start target clock hi, by rw [hw]; exact at_index head foot back j hj⟩

end TwoScans.BlockWire
#print axioms TwoScans.BlockWire.raw_code
