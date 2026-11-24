import HeaderBlocks

namespace TwoScans.PayloadBits
open WordBlocks TrackLayout HeaderBlocks BlockWire
open Label

variable {U C : Type}
abbrev L (U C : Type) := Label U C
def bodyLabels (us : List U) (vs : List C) : List (Label U C) :=
  [ub] ++ us.map site ++ [ue,ve] ++ vs.reverse.map color ++ [vb]

@[simp] theorem rev_body (us : List U) (vs : List C) : (reverseBody us vs).reverse = bodyLabels us vs := by
  simp [reverseBody,bodyLabels,List.reverse_append,List.append_assoc]

def payload (A : Alphabet (Label U C)) (us : List U) (vs : List C) (width : Nat) (foot : List Bool) :=
  List.replicate (width * A.width) true ++ [false] ++ chunks A (bodyLabels us vs) ++ foot

private theorem copies (n m : Nat) :
    List.replicate n true ++ List.replicate m true = List.replicate (n+m) true := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,Nat.succ_add]

theorem wire_payload (A : Alphabet (Label U C)) (wide start) (us : List U) (vs : List C)
    {w : Nat} (hw : 0 < w) (foot : List Bool) :
    wire (alphabet A wide start) [true] foot (back us vs w) = payload A us vs w foot := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0)
  unfold wire back payload
  simp only [List.reverse_append,List.reverse_replicate, List.reverse_cons,List.reverse_nil,
    List.nil_append, ←List.map_reverse, rev_body, Nat.succ_sub_one]
  simp only [chunks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.flatMap_map,alphabet,bits,List.append_assoc]
  have repeated : (List.replicate n (Group.run : Group (Label U C))).flatMap (bits A) =
      List.replicate (n*A.width) true := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ,ih,bits,Nat.succ_mul,Nat.add_comm]
  simp only [repeated]
  have e : true :: (List.replicate (n*A.width) true ++ List.replicate (A.width-1) true) =
      List.replicate ((n+1)*A.width) true := by
    rw [copies,←List.replicate_succ]
    congr 1
    rw [Nat.succ_mul]; omega
  simpa only [List.cons_append,List.nil_append,List.append_assoc] using
    congrArg (fun z => z ++ [false] ++ (bodyLabels us vs).flatMap A.code ++ foot) e

@[simp] theorem body_count (us : List U) (vs : List C) :
    (bodyLabels us vs).length = us.length+vs.length+4 := by
  simp [bodyLabels]; omega

@[simp] theorem back_count (us : List U) (vs : List C) {w} (hw : 0 < w) :
    (back us vs w).length = us.length+vs.length+4+w := by
  simp [back,reverseBody]; omega

/-- The suffix at the rear boundary is literally one known block and the footer. -/
theorem boundary (A : Alphabet (Label U C)) (us : List U) (vs : List C) (w) (foot) :
    let g := List.replicate (w*A.width) true ++ [false]
    let atB := g.length + ((bodyLabels us vs).length-1)*A.width
    (payload A us vs w foot).drop atB = A.code .vb ++ foot := by
  let front : List (Label U C) := [ub] ++ us.map site ++ [ue,ve] ++ vs.reverse.map color
  have h : bodyLabels us vs = front ++ [vb] := rfl
  unfold payload
  generalize (List.replicate (w * A.width) true ++ [false]) = head
  simp only [h,List.length_append,List.length_singleton,Nat.add_sub_cancel]
  rw [← chunks_len A front]
  change (head ++ ((front ++ [vb]).flatMap A.code) ++ foot).drop (head.length + (chunks A front).length) = _
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change (head ++ (chunks A front ++ A.code vb) ++ foot).drop _ = _
  have eq : head ++ (chunks A front ++ A.code vb) ++ foot = (head ++ chunks A front) ++ (A.code vb ++ foot) := by simp [List.append_assoc]
  rw [eq,← List.length_append, List.drop_left]

end TwoScans.PayloadBits
#print axioms TwoScans.PayloadBits.wire_payload
