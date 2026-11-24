import Std

/- Fixed-width binary blocks of the immutable payload, using false for A. -/
namespace TwoScans.WordBlocks

structure Alphabet (α : Type) where
  width : Nat
  positive : 0 < width
  code : α → List Bool
  length : ∀ a, (code a).length = width
  faithful : ∀ a b, code a = code b → a = b

variable {α : Type} (A : Alphabet α)

def chunks (xs : List α) := xs.flatMap A.code

@[simp] theorem chunks_len (xs : List α) : (chunks A xs).length = xs.length * A.width := by
  induction xs with
  | nil => simp [chunks]
  | cons a xs ih => simp_all [chunks, A.length, Nat.add_mul, Nat.add_comm]

theorem split_read (head : List Bool) (pre : List α) (a : α)
    (tail : List α) (footer : List Bool) :
    (((head ++ chunks A (pre ++ a :: tail) ++ footer).drop
       (head.length + pre.length * A.width)).take A.width) = A.code a := by
  rw [← chunks_len A pre]
  simp [chunks, List.append_assoc, List.drop_append, A.length, List.take_append]

theorem blocks_injective {u v : List α} (h : chunks A u = chunks A v) : u = v := by
  induction u generalizing v with
  | nil => cases v with
           | nil => rfl
           | cons b v =>
             have e := congrArg List.length h
             simp [chunks, A.length] at e
             have := A.positive
             omega
  | cons a u ih =>
    cases v with
    | nil =>
      have e := congrArg List.length h
      simp [chunks, A.length] at e
      have := A.positive
      omega
    | cons b v =>
      have e := congrArg (List.take A.width) h
      simp [chunks, A.length] at e
      have he := A.faithful a b e
      subst b
      change A.code a ++ chunks A u = A.code a ++ chunks A v at h
      exact congrArg (List.cons a) (ih (List.append_cancel_left h))

/-- The exact suffix and its fixed length force a unique scanner position. -/
theorem calibrate {word before footer : List Bool} {a : α} {age : Nat}
    (wordShape : word = before ++ A.code a ++ footer)
    (readout : word.drop age = A.code a ++ footer) : age = before.length := by
  have e := congrArg List.length readout
  simp [wordShape, A.length] at e
  have := A.positive
  omega

/-- The native word contains the encoded input at its right edge. An arbitrary
bit extension of that edge cannot counterfeit the label-aligned input suffix. -/
theorem anchored_suffix {xs ys : List α} {pre : List Bool} {foot : List Bool}
    (anchored : chunks A xs ++ foot = pre ++ chunks A ys ++ foot) :
    ∃ zs, xs = zs ++ ys := by
  have h := List.append_cancel_right (show chunks A xs ++ foot = (pre ++ chunks A ys) ++ foot by simpa [List.append_assoc] using anchored)
  have lens := congrArg List.length h
  simp only [chunks_len, List.length_append] at lens
  have ys_le : ys.length ≤ xs.length := by
    by_cases hle : xs.length < ys.length
    · have hmul := Nat.mul_lt_mul_of_pos_right hle A.positive
      omega
    · omega
  let n := xs.length - ys.length
  have hn : xs.length = n + ys.length := by dsimp [n]; omega
  have plen : pre.length = n * A.width := by
    rw [hn, Nat.add_mul] at lens
    omega
  have split := List.take_append_drop n xs
  have hcode : chunks A (xs.take n) ++ chunks A (xs.drop n) = pre ++ chunks A ys := by
    simpa only [chunks, List.flatMap_append] using (congrArg (chunks A) split).trans h
  have hd := congrArg (List.drop pre.length) hcode
  have hpre : (chunks A (xs.take n)).length = pre.length := by
    simp only [chunks_len, List.length_take, plen]
    rw [Nat.min_eq_left (by dsimp [n]; omega)]
  rw [←hpre] at hd
  simp only [List.drop_left] at hd
  rw [hpre, List.drop_left] at hd
  exact ⟨xs.take n, split.symm.trans (congrArg _ (blocks_injective A hd))⟩

end TwoScans.WordBlocks
#print axioms TwoScans.WordBlocks.anchored_suffix
