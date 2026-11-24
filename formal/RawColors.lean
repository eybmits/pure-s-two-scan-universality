import PayloadBits
import ObserverBlocks

namespace TwoScans.RawColors
open Term Frames Observer WordBlocks TrackLayout HeaderBlocks BlockWire PayloadBits

variable {U C : Type}
abbrev Lab := Label U C

def position (N s j : Nat) := 1+(N-1-j)*s

theorem position_clock {N s j : Nat} (h : j < N) :
    position N s j + j*s = position N s 0 := by
  have z : N-1-j+j=N-1 := by omega
  have q := congrArg (· * s) z
  simp only [Nat.add_mul] at q
  simp only [position,Nat.sub_zero]
  omega

/-- Reading at a calibrated block index in an actual payload returns the
corresponding body label. Reads in the unary header fail to decode. -/
theorem read_label (g : Term) (A : Alphabet (Label U C)) (wide : 1 < A.width) (starts : ∀ a, (A.code a).head? = some false)
    (decode : List Bool → Option (Label U C))
    (decode_spec : ∀ b a, decode b = some a ↔ A.code a = b)
    (classify : Term → Option (Label U C) × Bool) (foot : List Bool)
    (classifier : ∀ w, classify (word g w) =
      (decode (w.take A.width),decide (w = A.code .vb ++ foot)))
    (us : List U) (vs : List C) {w : Nat} (hw : 0 < w)
    (j) (hj : j < (back us vs w).length) :
    let p := payload A us vs w foot
    let i := position (back us vs w).length A.width j
    (observedAt g classify p i).bind (fun a => a.1) = (reverseBody us vs)[j]? := by
  let A' := alphabet A wide starts
  let b := back us vs w
  let p := payload A us vs w foot
  let q := position b.length A.width j
  change j < b.length at hj
  have wp : wire A' [true] foot b = p := wire_payload A wide starts us vs hw foot
  have live : q < p.length := by
    rw [← wp,length_wire]
    have hm := Nat.mul_lt_mul_of_pos_right (show b.length-1-j < b.length by omega) A.positive
    change 1+(b.length-1-j)*A.width < 1+b.length*A.width+foot.length
    omega
  have read : ((p.drop q).take A.width) = bits A b[j] := by
    rw [← wp]; exact at_index (A := A') [true] foot b j hj
  change (observedAt g classify p q).bind _ = _
  rw [show observedAt g classify p q = some (classify (word g (p.drop q))) from by simp [observedAt,live]]
  simp only [Option.bind_some,classifier,read]
  rw [← back_read us vs w j, List.getElem?_eq_getElem hj]
  generalize b[j] = entry
  change decode (bits A entry) = ungroup (some entry)
  cases entry with
  | data a => apply (decode_spec _ _).mpr rfl
  | run =>
    cases e : decode (bits A (.run : Group (Label U C))) with
    | none => rfl
    | some a =>
      have eq := (decode_spec _ _).mp e
      have bad := A'.faithful (.data a) .run eq
      cases bad
  | delimiter =>
    cases e : decode (bits A (.delimiter : Group (Label U C))) with
    | none => rfl
    | some a =>
      have eq := (decode_spec _ _).mp e
      have bad := A'.faithful (.data a) .delimiter eq
      cases bad

theorem boundary_pos (A : Alphabet (Label U C)) (us : List U) (vs : List C)
    {w : Nat} (hw : 0 < w) :
    position (back us vs w).length A.width 0 =
      (List.replicate (w*A.width) true ++ [false]).length +
      ((bodyLabels us vs).length-1)*A.width := by
  rw [back_count us vs hw,body_count]
  have eq : us.length+vs.length+4+w-1=(us.length+vs.length+4-1)+w := by omega
  simp [position,Nat.add_mul]; omega

/-- The single successful rear-boundary observation forces its literal bit
position. This also handles late or exhausted reads. -/
theorem calibration_iff (g : Term) (A : Alphabet (Label U C))
    (classify : Term → Option (Label U C) × Bool) (foot : List Bool)
    (classifier : ∀ w, (classify (word g w)).2 = decide (w = A.code .vb ++ foot))
    (us : List U) (vs : List C) {w : Nat} (hw : 0 < w) (j) :
    let p := payload A us vs w foot
    ((observedAt g classify p j).map Prod.snd).getD false = true ↔
      j = position (back us vs w).length A.width 0 := by
  let p := payload A us vs w foot
  let z := position (back us vs w).length A.width 0
  have known : p.drop z = A.code .vb ++ foot := by
    dsimp only [p,z]; rw [boundary_pos A us vs hw]; exact boundary A us vs w foot
  have good : z < p.length := by
    have h := congrArg List.length known
    simp only [List.length_drop,List.length_append,A.length] at h
    have := A.positive
    omega
  change ((observedAt g classify p j).map Prod.snd).getD false = true ↔ j = z
  by_cases hj : j < p.length
  · simp only [observedAt,ite_eq_left hj,Option.map_some,Option.getD_some,classifier,decide_eq_true_eq]
    constructor
    · intro e
      have h := congrArg List.length (e.trans known.symm)
      simp only [List.length_drop] at h; omega
    · rintro rfl; exact known
  · simp [observedAt,hj]; omega

end TwoScans.RawColors
#print axioms TwoScans.RawColors.calibration_iff
#print axioms TwoScans.RawColors.read_label
