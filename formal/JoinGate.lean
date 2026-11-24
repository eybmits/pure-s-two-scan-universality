import RawColors
import ObserverGate
import TableauTracks
import Shell

namespace TwoScans.Join
open Term Frames Automata Observer Tableau TrackLayout WordBlocks PayloadBits RawColors Shell
variable {R C : Type} [DecidableEq C] [FinStates (Label R C)]

def gate (A : Alphabet (Label R C)) (cur : R → C) (next : R → Option C)
    (foot : List Bool) (slow : Bool) (t : Term) :=
  (evaluate g (classifier g A .vb foot) (blockControl A.width slow (checks A cur next slow)) t).1 none

def both (A : Alphabet (Label R C)) (cur : R → C) (next : R → Option C)
    (foot : List Bool) (t : Term) := gate A cur next foot false t && gate A cur next foot true t

theorem regular_both (A : Alphabet (Label R C)) (cur : R → C) (next : R → Option C)
    (foot : List Bool) : Regular (fun t => both A cur next foot t = true) := by
  let f := gate A cur next foot false
  let s := gate A cur next foot true
  have ar (b : Bool) : Attribute (gate A cur next foot b) :=
    boolAttribute (route_regular g _ (classifier_attribute g A .vb foot) _ none)
  obtain ⟨Q,iq,fold,out,eq⟩ := attrPair (ar false) (ar true)
  exact ⟨Q,iq,fold,fun q => (out q).1 && (out q).2,fun t => by dsimp only; rw [eq]; rfl⟩

def headTime (s w : Nat) (slow : Bool) := 1 + (w*s)*(if slow then 2 else 1)
def base (N s : Nat) := position N s 0 + s + 1

/-- With the rear probe calibrated, every requested bit index has one
common formula for the fast and slow controller. -/
private theorem index_eq {N s w k} (slow : Bool) (valid : k+(if slow then w else 0) < N) :
    base N s - (if slow then w*s else 0) - ((k+1)*s+1) =
      position N s (k+(if slow then w else 0)) := by
  have eq := position_clock (s := s) valid
  cases slow <;> simp only [base,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero,Nat.add_mul,
    Nat.one_mul,Nat.sub_zero] at * <;> omega

private theorem enough {n m w s : Nat} (hw : 0 < w) (slow : Bool) :
    (n+2)*s+1 ≤ base (n+m+4+w) s - (if slow then w*s else 0) := by
  have f : n+m+4+w-1=n+m+3+w := by omega
  unfold base position
  simp only [Nat.sub_zero,f,Nat.add_mul]
  cases slow <;> simp <;> omega

def Tests (cur : R → C) (next : R → Option C) (us : List R) (vs : List C) (w : Nat) :=
  let b := reverseBody us vs
  b[us.length+1]? = some .ve ∧
    (∀ i (h : i < us.length), readColor b[i+1]? = some (cur us[i])) ∧
    (∀ i (h : i < us.length), readColor b[i+w+1]? = next us[i])

private theorem gate_spec (A : Alphabet (Label R C)) (ends : ∀ a, ∃ ds, A.code a = ds ++ [true])
    (us : List R) (vs : List C) (w) (foot) (cur : R → C) (next : R → Option C) (s : Bool) (age) :
    let p := payload A us vs w foot
    gate A cur next foot s (body p age) = true ↔
    ready p + headTime A.width w s ≤ age ∧ GoodSamples A.width cur next s us
      (observedAt g (classifier g A .vb foot) p) (age-ready p-headTime A.width w s) :=
  gate_packet tagger_nf (by decide : 3 ≤ size g) A ends us vs w foot cur next s age

theorem checked_tests (A : Alphabet (Label R C)) (wide : 1 < A.width)
    (starts : ∀ a, (A.code a).head? = some false) (ends : ∀ a, ∃ ds, A.code a = ds ++ [true])
    (cur : R → C) (next : R → Option C) (foot) (us : List R) (vs : List C) (w)
    (hw : 0 < w) :
    (∃ age, both A cur next foot (body (payload A us vs w foot) age) = true) ↔
      Tests cur next us vs w := by
  let p := payload A us vs w foot
  let s := A.width
  let N := (HeaderBlocks.back us vs w).length
  let obs := observedAt g (classifier g A .vb foot) p
  let t := base N s
  have ndef : N = us.length+vs.length+4+w := back_count us vs hw
  have at0 (j : Nat) : ((obs j).map Prod.snd).getD false = true ↔ j = position N s 0 :=
    calibration_iff g A _ foot (fun b => congrArg Prod.snd (classifier_word g A .vb foot b)) us vs hw j
  have read (slow : Bool) (k : Nat) (hk : k ≤ us.length+1) :
      (sample s obs (t-(if slow then w*s else 0)) k).bind Prod.fst =
      (reverseBody us vs)[k+(if slow then w else 0)]? := by
    have bound : k+(if slow then w else 0) < N := by cases slow <;> simp <;> omega
    unfold sample
    rw [show t-(if slow then w*s else 0)-((k+1)*s+1) = _ from index_eq slow bound]
    exact read_label g A wide starts (decodeBits A) (decodeBits_some A) _ foot
      (classifier_word g A .vb foot) us vs hw _ bound
  have en (slow : Bool) : (us.length+2)*s+1 ≤ t-(if slow then w*s else 0) := by
    unfold t; rw [ndef]; exact enough hw slow
  have ht (slow : Bool) : headTime s w slow = headTime s w false + (if slow then w*s else 0) := by
    cases slow <;> simp [headTime] <;> omega
  have calibrated {age : Nat} (fastOK : gate A cur next foot false (body p age) = true) :
      age = ready p + headTime s w false + t := by
    obtain ⟨h0,hsize,hstart,_⟩ := (gate_spec A ends us vs w foot cur next false age).mp fastOK
    change (us.length+2)*s+1 ≤ age-ready p-headTime s w false at hsize
    change ((obs ((age-ready p-headTime s w false) - ((0+1)*s+1))).map Prod.snd).getD false = true at hstart
    have e := (at0 _).mp hstart
    have z := Nat.mul_le_mul_right s (show 1 ≤ us.length+2 by omega)
    change age = ready p + headTime s w false + (position N s 0 + s + 1)
    change ready p + headTime s w false ≤ age at h0
    simp only [Nat.zero_add,Nat.one_mul] at e z
    omega
  let when := ready p + headTime s w false + t
  have evaluateAt (slow : Bool) :
      gate A cur next foot slow (body p when) = true ↔
      GoodSamples s cur next slow us obs (t-(if slow then w*s else 0)) := by
    have gateLaw := gate_spec A ends us vs w foot cur next slow when
    dsimp only at gateLaw
    rw [gateLaw]
    have spare : (if slow then w*s else 0) ≤ t := by
      cases slow with
      | false => simp
      | true =>
        simp
        unfold t base position
        rw [ndef]
        have hmul := Nat.mul_le_mul_right s (show w ≤ us.length+vs.length+4+w-1-0 by omega)
        omega
    change (ready p+headTime s w slow ≤ when ∧
      GoodSamples s cur next slow us obs (when-ready p-headTime s w slow)) ↔ _
    rw [ht]
    simp only [when]
    have e : ready p + headTime s w false + t - ready p -
      (headTime s w false + (if slow then w*s else 0)) = t-(if slow then w*s else 0) := by omega
    rw [e]; exact and_iff_right (by omega)
  have pair : (∃ age, both A cur next foot (body p age) = true) ↔
    GoodSamples s cur next false us obs t ∧ GoodSamples s cur next true us obs (t-w*s) := by
    constructor
    · rintro ⟨age,h⟩
      change (gate A cur next foot false _ && gate A cur next foot true _) = true at h
      obtain ⟨f,h⟩ := (Bool.and_eq_true_iff).mp h
      obtain rfl := calibrated f
      exact ⟨by simpa only [Bool.false_eq_true,ite_false,Nat.sub_zero] using (evaluateAt false).mp f,
        (evaluateAt true).mp h⟩
    · rintro ⟨hf,hs⟩
      exact ⟨when,Bool.and_eq_true_iff.mpr ⟨(evaluateAt false).mpr (by simpa using hf),(evaluateAt true).mpr hs⟩⟩
  rw [pair]
  have startsOK : beginOK false (sample s obs t 0) = true := by
    apply (at0 _).mpr; simp [t,base]
  have fRead (k) (hk : k ≤ us.length+1) := read false k hk
  have sRead (k) (hk : k ≤ us.length+1) := read true k hk
  simp only [Bool.false_eq_true,ite_false,Nat.sub_zero,Nat.add_zero,ite_true] at fRead sRead
  have ff : (us.length+2)*s+1 ≤ t := by simpa using en false
  have ss : (us.length+2)*s+1 ≤ t-w*s := en true
  unfold GoodSamples Tests
  simp only [ff,ss,startsOK,show ∀ v : Reading R C, beginOK true v = true from fun _ => rfl, Bool.true_or,true_and,siteOK,ite_true,
    Bool.false_eq_true,ite_false,decide_eq_true_eq,endOK,Bool.false_or]
  have endEq := fRead (us.length+1) (Nat.le_refl _)
  rw [endEq]
  constructor
  · rintro ⟨⟨f,hf⟩,sl,_⟩
    refine ⟨?_,?_,?_⟩
    · cases e : (reverseBody us vs)[us.length+1]? with
      | none => simp [e] at hf
      | some a => cases a <;> simp_all
    · intro i hi; rw [← fRead (i+1) (by omega)]; exact f i hi
    · intro i hi
      rw [show i+w+1=(i+1)+w by omega,← sRead (i+1) (by omega)]
      exact sl i hi
  · rintro ⟨boundaryTest,fastTest,slowTest⟩
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · intro i hi; rw [fRead (i+1) (by omega)]; exact fastTest i hi
    · simp [boundaryTest]
    · intro i hi; rw [sRead (i+1) (by omega)]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using slowTest i hi
    · trivial

theorem both_iff {K : Type} [DecidableEq K] [FinStates (Label (Site K) (Option K))]
    (A : Alphabet (Label (Site K) (Option K))) (wide : 1 < A.width)
    (starts : ∀ a, (A.code a).head? = some false) (ends : ∀ a, ∃ ds, A.code a = ds ++ [true])
    (foot : List Bool) (us : List (Site K)) (vs : List (Option K)) (w : Nat) (hw : 0 < w) :
    (∃ age, both A Site.current Site.expected foot (body (payload A us vs w foot) age) = true) ↔
      TrackTests us vs w := checked_tests A wide starts ends _ _ foot us vs w hw

end TwoScans.Join
#print axioms TwoScans.Join.checked_tests
