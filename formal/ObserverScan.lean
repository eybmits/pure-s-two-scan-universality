import Scan
import Live

namespace TwoScans.Observer
open Term Frames Scan

/-- Syntax-only recognizers for wrapper words and scanner operands. -/
def isWord (g : Term) : Term → Bool
  | .s => false
  | .app h a => if h = s then a == g else (h == A || h == B) && isWord g a

theorem isWord_spec (g t : Term) : isWord g t = true ↔ ∃ bs, t = word g bs := by
  induction t with
  | s =>
    constructor
    · simp [isWord]
    · rintro ⟨_ | ⟨b,bs⟩, h⟩
      · cases h
      · cases b <;> cases h
  | app h a _ ih =>
    constructor
    · simp only [isWord]
      split
      · rintro ha
        exact ⟨[], by simp_all [word]⟩
      · simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,ih]
        rintro ⟨(rfl | rfl),bs,rfl⟩
        · exact ⟨false::bs,rfl⟩
        · exact ⟨true::bs,rfl⟩
    · rintro ⟨_ | ⟨b,bs⟩, eq⟩
      · cases eq; simp [isWord]
      · cases b <;> cases eq <;> simp [isWord,A,B,ih] <;> exact ⟨bs,rfl⟩

def isUnaryWord (g : Term) : Term → Bool
  | .app .s a => isWord g a
  | _ => false

def isV (g : Term) : Term → Bool
  | .app l r => isUnaryWord g l && isUnaryWord g r
  | _ => false

theorem unaryWord_spec (g t) : isUnaryWord g t = true ↔ ∃ bs, t = s ⋆ word g bs := by
  cases t with
  | s => simp [isUnaryWord]
  | app l a =>
    cases l with
    | s => simp [isUnaryWord,isWord_spec]
    | app _ _ => simp [isUnaryWord]

theorem isV_spec (g t) : isV g t = true ↔ VClass g t := by
  cases t with
  | s => simp [isV,VClass,operand]
  | app l r =>
    simp only [isV, Bool.and_eq_true,unaryWord_spec,VClass,operand,Term.app.injEq]
    constructor
    · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩; exact ⟨a,b,ha,hb⟩
    · rintro ⟨a,b,ha,hb⟩; exact ⟨⟨a,ha⟩,⟨b,hb⟩⟩

/-- Returns the term at the first valid site along the frame spine. The caller
    only inspects bounded prefixes or a fixed-width terminal block. -/
def read (g : Term) : Term → Option Term
  | .app (.app h a) r =>
    if (h == A || h == B) && isWord g a && isV g r then some (h ⋆ a)
    else if (h == s || h == A) && isV g a then read g r else none
  | _ => none

theorem read_site {g t z} (h : read g t = some z) :
    ∃ r b a, Occ (z ⋆ r) t ∧ z = word g (b::a) ∧ VClass g r := by
  induction t with
  | s => simp [read] at h
  | app l r _ ih =>
    cases l with
    | s => simp [read] at h
    | app k a =>
      simp only [read] at h
      split at h
      next accept =>
        simp only [Option.some.injEq] at h
        subst z
        simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,isWord_spec,isV_spec] at accept
        obtain ⟨⟨hk,bs,rfl⟩,hr⟩ := accept
        rcases hk with rfl | rfl
        · exact ⟨r,false,bs,.here,rfl,hr⟩
        · exact ⟨r,true,bs,.here,rfl,hr⟩
      next =>
        split at h
        · obtain ⟨v,b,bs,o,hs,hv⟩ := ih h; exact ⟨v,b,bs,.right o,hs,hv⟩
        · cases h

theorem word_is_not_V {g} (big : 3 ≤ size g) (bs) : isV g (word g bs) = false := by
  cases he : isV g (word g bs) with
  | false => rfl
  | true => exact (noOperandInWord big ((isV_spec _ _).1 he) bs .here).elim

theorem V_is_not_word {g v} (big : 3 ≤ size g) (hv : VClass g v) : isWord g v = false := by
  cases he : isWord g v with
  | false => rfl
  | true =>
    obtain ⟨bs,rfl⟩ := (isWord_spec _ _).1 he
    exact (noOperandInWord big hv bs .here).elim

theorem read_stack {g v} (big : 3 ≤ size g) (hv : VClass g v) (pre) (t) :
    read g (Scan.stack v pre t) = read g t := by
  induction pre with
  | nil => rfl
  | cons b pre ih =>
    have nword := V_is_not_word big hv
    have yes := (isV_spec _ _).2 hv
    cases b <;> simp [Scan.stack,Scan.frame,read,A,B,nword,yes,ih]

def probeV (g : Term) (w : List Bool) := operand (word g w) (word g w)

theorem read_inside {g} (hg : nf g = true) (big : 3 ≤ size g) (pre : List Bool) (b : Bool) (tail) :
    let w := pre ++ b::tail
    read g (rounds pre.length (word g w ⋆ probeV g w)) = some (word g (b::tail)) := by
  dsimp only
  let v := probeV g (pre ++ b :: tail)
  have hv : VClass g v := ⟨_,_,rfl⟩
  have hnf : nf v = true := by simp [v,probeV,operand,nf,root,word_normal hg]
  rw [(peel hg hnf pre (b::tail)).result,read_stack big hv]
  have yes := (isV_spec _ _).2 hv
  have hw := (isWord_spec g (word g tail)).2 ⟨_,rfl⟩
  cases b <;> simp [word,read,hw,yes,v]

theorem read_exhausted {g} (hg : nf g = true) (big : 3 ≤ size g) (w) (j : Nat)
    (late : w.length ≤ j) : read g (rounds j (word g w ⋆ probeV g w)) = none := by
  cases he : read g (rounds j (word g w ⋆ probeV g w)) with
  | none => rfl
  | some z =>
    obtain ⟨v,b,bs,o,rfl,hv⟩ := read_site he
    rw [← Nat.add_sub_of_le late, rounds_add] at o
    cases b <;> exact ((noFalseScanAfterEnd hg big w (j-w.length) hv o) (Step.root _ _ _)).elim

theorem read_exact {g} (hg : nf g = true) (big : 3 ≤ size g) (w) (j : Nat) :
    read g (rounds j (word g w ⋆ probeV g w)) =
      if j < w.length then some (word g (w.drop j)) else none := by
  split
  next hj =>
    have cut := List.take_append_drop j w
    have len : (w.take j).length = j := by simp; omega
    cases eq : w.drop j with
    | nil =>
      have : (w.drop j).length = w.length - j := List.length_drop
      rw [eq] at this
      simp at this
      omega
    | cons b tail =>
      rw [eq] at cut
      simpa only [len,cut] using read_inside hg big (w.take j) b tail
  next hj => exact read_exhausted hg big _ _ (by omega)

#print axioms read_exact
end TwoScans.Observer
