import ObserverBlocks

namespace TwoScans.Observer
open Term Frames Scan Generation Live Automata TrackLayout WordBlocks

private theorem blockEarly {X} (g : Term) (classify : Term → X) (p : List Bool)
    (s) (slow : Bool) (check : Bool → List Bool → Option X → Action Bool)
    (first : Bool) (pre : Short s) (digits w : List Bool) (j : Nat)
    (full : pre.1.length + digits.length + 1 = s) (early : j < digits.length + 2) :
    wordControl g classify (blockControl s slow check) p (digits ++ true::w) j (some (first,pre)) = false := by
  induction digits generalizing pre j with
  | nil =>
    have hj : j = 0 ∨ j = 1 := by simp at early; omega
    rcases hj with rfl | rfl <;> rfl
  | cons b ds ih =>
    have hs : pre.1.length + 1 < s := by simp at full; omega
    let n : Short s := ⟨pre.1 ++ [b],by simp; omega⟩
    have hnext : n.val.length + ds.length + 1 = s := by
      calc
        _ = pre.val.length+(b::ds).length+1 := by simp [n]; omega
        _ = s := full
    cases j with
    | zero => cases b <;> rfl
    | succ j =>
      cases j with
      | zero =>
        cases b with
        | true => rfl
        | false =>
          simp [wordControl,blockControl,ingest,hs,perform]
      | succ j =>
        rw [List.cons_append,prefixStep g classify p s slow check first pre b (ds ++ true::w) j (by simpa using hs)]
        apply ih
        · exact hnext
        · simp at early; omega

private theorem headerEarly {X} (g : Term) (classify : Term → X) (p : List Bool)
    (s) (slow : Bool) (check : Bool → List Bool → Option X → Action Bool)
    (n : Nat) (w : List Bool) (t : Nat) (early : t < 1 + n * (if slow then 2 else 1)) :
    wordControl g classify (blockControl s slow check) p (List.replicate n true ++ false::w) t none = false := by
  induction n generalizing t with
  | zero =>
    obtain rfl : t = 0 := by simpa using early
    rfl
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append]
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        cases slow with
        | false =>
          simpa [wordControl,blockControl,perform] using ih (t+1) (by simp_all; omega)
        | true => simpa [wordControl,blockControl,perform] using ih t (by simp_all [Nat.add_mul]; omega)

/-- The color/check flag available at each B block end, after crossing a header.
    This includes the absence of a scan result beyond the available word. -/
def blockRun {R X} (A : Alphabet R) (g : Term) (classify : Term → X) (p : List Bool)
    (check : Bool → List Bool → Option X → Action Bool)
    (endRun : Nat → Bool → Bool) : List R → Nat → Bool → Bool
  | [], t, first => endRun t first
  | a::rest, t, first =>
    if t < A.width + 1 then false else
    let age := t-(A.width+1)
    let after := blockRun A g classify p check endRun rest (t-A.width)
    perform (check first (A.code a) (observedAt g classify p age)) after after

theorem blocks_exact {R X} (A : Alphabet R) (ends : ∀ a, ∃ digits, A.code a = digits ++ [true])
    (g : Term) (classify : Term → X) (p : List Bool) (slow : Bool)
    (check : Bool → List Bool → Option X → Action Bool) (rs : List R) (tail : List Bool) (j first) :
    let c := blockControl A.width slow check
    wordControl g classify c p (chunks A rs ++ tail) j (checking A.width first) =
      blockRun A g classify p check (fun t f => wordControl g classify c p tail t (checking A.width f))
        rs j first := by
  induction rs generalizing j first with
  | nil => rfl
  | cons a rs ih =>
    obtain ⟨ds,hds⟩ := ends a
    have hlen := A.length a
    rw [hds,List.length_append] at hlen
    have full : ds.length + 1 = A.width := hlen
    let rest := chunks A rs ++ tail
    have shape : chunks A (a::rs) ++ tail = ds ++ true::rest := by simp [chunks,hds,rest,List.append_assoc]
    dsimp only
    rw [shape]
    by_cases hj : j < A.width + 1
    · simp only [checking]
      rw [blockEarly g classify p A.width slow check first (blank _) ds rest j (by simpa [blank] using full) (by omega)]
      simp [blockRun,hj]
    · let age := j - (A.width+1)
      have eq : j = age+2+ds.length := by dsimp [age]; omega
      have rem : age+1 = j-A.width := by dsimp [age]; omega
      have run := blockStep g classify p A.width slow check first (blank _) ds rest age (by simpa [blank] using full)
      rw [←eq] at run
      simp only [blank,List.nil_append,←hds,rem] at run
      simp only [checking,blank] at *
      rw [run]
      unfold rest
      simp only [blockRun,ite_eq_right hj,age,ih]

theorem header_exact {X} (g : Term) (classify : Term → X) (p : List Bool)
    (s) (slow : Bool) (check : Bool → List Bool → Option X → Action Bool)
    (n : Nat) (w : List Bool) (t : Nat) :
    let cost := 1 + n * (if slow then 2 else 1)
    wordControl g classify (blockControl s slow check) p (List.replicate n true ++ false::w) t none =
      if t < cost then false else
      wordControl g classify (blockControl s slow check) p w (t-cost) (checking s true) := by
  dsimp only
  by_cases h : t < 1 + n * (if slow then 2 else 1)
  · rw [ite_eq_left h]; exact headerEarly g classify p s slow check n w t h
  · rw [ite_eq_right h]
    have hsum : t-(1+n*(if slow then 2 else 1))+1+n*(if slow then 2 else 1) = t := by omega
    simpa only [hsum] using headerStep g classify p s slow check n w (t-(1+n*(if slow then 2 else 1)))

#print axioms blocks_exact
#print axioms header_exact
end TwoScans.Observer
