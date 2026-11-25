import TraceSelect
import InitialRowCode
import SerialTrace

namespace TwoScans.Chronology
open Automata Tableau Tableau.OneTape Frames AnyTape SerialTrace

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- A canonical tape row retains the head and every cell to its left. The right boundary
    marker and redundant blanks to the right of the head are suppressed. -/
def canonical (blank : Γ) : List (Color Q Γ) → List (Color Q Γ)
  | [] => []
  | x::xs => let r := canonical blank xs
             if r.isEmpty && (decide (x = .wall) || decide (x = .plain blank)) then [] else x::r

private theorem canon_append (blank : Γ) (xs ys : List (Color Q Γ))
    (h : canonical blank ys = []) : canonical blank (xs ++ ys) = canonical blank xs := by
  induction xs with
  | nil => exact h
  | cons x xs ih => simp only [List.cons_append,canonical,ih]

private theorem canon_suffix (blank : Γ) (k : Nat) :
    canonical (Q:=Q) blank (List.replicate k (.plain blank) ++ [.wall]) = [] := by
  induction k with
  | zero => simp [canonical]
  | succ k ih => simp [List.replicate_succ,canonical,ih]

@[simp] theorem canonical_pad (blank : Γ) (c : Cfg Q Γ) (k : Nat) :
    canonical blank (encode (pad blank c k)) = canonical blank (encode c) := by
  let base : List (Color Q Γ) := c.left.reverse.map Color.plain ++ .head c.state c.here :: c.right.map Color.plain
  have split : encode (pad blank c k) = base ++ (List.replicate k (.plain blank) ++ [.wall]) := by
    simp [base,encode,pad,List.append_assoc]
  have split' : encode c = base ++ [.wall] := by simp [base,encode,List.append_assoc]
  rw [split,split',canon_append _ _ _ (canon_suffix blank k)]
  exact (canon_append blank base [.wall] (by simp [canonical])).symm

variable [FinStates Q] [FinStates Γ]

def seed (blank : Γ) (c : Cfg Q Γ) : Term :=
  start (InitialRowCode.raw (encode c)) (startTerm blank c)

/-- A single-valued current-tree reader. The index is part of its output. -/
def reader (δ : Table Q Γ) (blank : Γ) (t : Term) :=
  (read (InitialRowCode.decode (Color Q Γ)) (TraceSelect.readAt δ blank) t).map
    (fun p => (p.1,canonical blank p.2))

/-- Under the fixed left-to-right serialization of innermost rounds, one strictly
    increasing sequence of *individual contraction indices* reads the entire run,
    starting at zero. At all other indices any reported pair is still correct. -/
theorem trajectory (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) :
    let e := seed blank c
    let row := fun n => canonical blank (encode (run (advance δ blank) c n))
    (∀ j t n y, At e j t → reader δ blank t = some (n,y) → y = row n) ∧
    ∃ time : Nat → Nat, time 0 = 0 ∧ (∀ n, time n < time (n+1)) ∧
       ∀ n, ∃ t, At e (time n) t ∧ reader δ blank t = some (n,row n) := by
  dsimp only
  let V := fun i (y : List (Color Q Γ)) => ∃ k, y = encode (pad blank (run (advance δ blank) c i) k)
  let a := InitialRowCode.raw (encode c)
  have good (n k : Nat) (y) (h : TraceSelect.readAt δ blank k (rounds n (startTerm blank c)) = some y) :
      V k y := TraceSelect.readAt_sound δ blank c n k y h
  have base (y) (h : InitialRowCode.decode (Color Q Γ) a = some y) : V 0 y := by
    have ey : encode c = y := Option.some.inj (InitialRowCode.decode_raw (encode c) |>.symm.trans h)
    subst y; exact ⟨0,by simp [pad,run]⟩
  have bare {j t i y} (obs : At (seed blank c) j t)
      (h : read (InitialRowCode.decode (Color Q Γ)) (TraceSelect.readAt δ blank) t = some (i,y)) : V i y :=
    all_samples _ _ V (InitialRowCode.sweep_raw _) (InitialRowCode.parallel_raw _) base good obs h
  constructor
  · intro j t n y atT decoded
    obtain ⟨⟨i,r⟩,h,eq⟩ := Option.map_eq_some_iff.mp decoded
    cases eq
    obtain ⟨k,rfl⟩ := bare atT h
    exact canonical_pad ..
  · have cofinal (i T : Nat) : ∃ b y, T < b ∧ TraceSelect.readAt δ blank i
        (rounds b (startTerm blank c)) = some y := by
      obtain ⟨b,late,allRows⟩ := TraceSelect.readAt_cofinal δ blank c i T
      obtain ⟨k,yes⟩ := allRows i (Nat.le_refl i)
      exact ⟨b,_,late,yes⟩
    obtain ⟨time,zero,rise,gets⟩ := chronological (InitialRowCode.decode (Color Q Γ))
      (TraceSelect.readAt δ blank) (InitialRowCode.sweep_raw (encode c)) (InitialRowCode.parallel_raw _)
      (encode c) (InitialRowCode.decode_raw _) cofinal
    refine ⟨time,zero,rise,?_⟩
    intro n
    obtain ⟨t,y,atT,hit⟩ := gets n
    obtain ⟨k,rfl⟩ := bare atT hit
    exact ⟨t,atT,by simp [reader,hit]⟩

/-- Fixed tables and the constant clock change only the constants of the linear input bound. -/
theorem linear_seed (blank : Γ) : ∃ a b : Nat, ∀ c : Cfg Q Γ,
    size (seed blank c) ≤ a + b * (c.left.length + 1 + c.right.length) := by
  let aux := (FiniteCodes.alphabet (Color Q Γ)).width
  let blocks := (A Q Γ).width
  refine ⟨2 * size SerialTrace.clock + 3 * size Shell.g + 5 + 3 * aux + 9 * blocks,
      3 * aux + 3 * blocks, ?_⟩
  intro c
  let len := c.left.length + 1 + c.right.length
  have lenEq : (encode c).length = len+1 := by simp [encode,len]; omega
  have h1 := InitialRowCode.size_raw (encode c)
  rw [lenEq] at h1
  change size (InitialRowCode.raw (encode c)) ≤ size Shell.g + 1 + 3 * aux * (len+1) at h1
  have h2 := size_start blank c
  change size (startTerm blank c) ≤ 2*size Shell.g + 1 + 3*((len+3)*blocks) at h2
  change _ ≤ _ + (3 * aux + 3 * blocks) * len
  simp only [seed,SerialTrace.start,SerialTrace.frame,SerialTableau.pack,size,Nat.add_mul]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at h1 h2
  simp only [Nat.mul_comm len blocks,Nat.mul_assoc] at *
  omega

end TwoScans.Chronology
#print axioms TwoScans.Chronology.trajectory
#print axioms TwoScans.Chronology.linear_seed
