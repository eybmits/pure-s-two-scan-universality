import TableauCandidate
import ShellLanguages

namespace TwoScans.Tableau.Certificate
open Term Frames Shell WordBlocks PayloadBits Automata OneTape
variable {Q Z : Type} [DecidableEq Q] [DecidableEq Z]

/-- Exact composition interface. Both conditions refer to raw Boolean
functions on input trees or bit strings; no test can consult the source run. -/
structure Tests (A : Alphabet (Letter Q Z)) (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q) where
  wordTest : List Bool → Bool
  bodyTest : Term → Bool
  decode : List Bool → List Bool
  wordSpec : ∀ raw, wordTest raw = true ↔ ∃ us vs w,
    raw = payload A us vs w [] ∧ 0 < w ∧ rowsOK (stopped δ halt) halt q us = true
  gateSpec : ∀ us vs w (_ : 0 < w),
    (∃ age, bodyTest (body (payload A us vs w []) age) = true) ↔ TrackTests us vs w
  decodeSpec : ∀ us vs w, 0 < w →
    decode (payload A us vs w []) = Static.outBits valueCell us
  regularWord : Language.Reg (fun raw => wordTest raw = true)
  regularBody : Regular (fun t => bodyTest t = true)

def Tests.report {δ : Table Q (Symbol Z)} {A : Alphabet (Letter Q Z)} {halt q}
    (t : Tests A δ halt q) := first (localReport t.wordTest t.bodyTest t.decode)

theorem Tests.regular_report {δ : Table Q (Symbol Z)} {A : Alphabet (Letter Q Z)} {halt q}
    (t : Tests A δ halt q) : Regular (fun r => ∃ y, t.report r = some y) := by
  obtain ⟨K,inst,k,f,a,h⟩ := t.regularWord
  haveI := inst
  obtain ⟨X,ix,F,ok,hf⟩ := regular_word g k f a
  apply regular_first _ _ _ _ t.regularBody
  exact ⟨X,ix,F,ok,fun r => by rw [hf]; simp only [h]⟩

theorem Tests.sound {δ : Table Q (Symbol Z)} {A : Alphabet (Letter Q Z)} {halt q}
    (t : Tests A δ halt q) (x y : List Bool) (n : Nat)
    (hit : t.report (rounds n (seed (anchor A q x))) = some y) : Computes δ halt q x y := by
  obtain ⟨extra,age,wp,bp,out⟩ := first_output_sound _ _ _ _ _ _ hit
  obtain ⟨us,vs,w,raw,hw,rows⟩ := (t.wordSpec _).mp wp
  rw [raw] at bp out
  have probes := (t.gateSpec us vs w hw).mp ⟨age,bp⟩
  exact (accepted_iff_computes A δ halt q x y).mp
    ⟨extra,us,vs,w,raw,hw,rows,probes,(t.decodeSpec us vs w hw).symm.trans out⟩

theorem Tests.complete {δ : Table Q (Symbol Z)} {A : Alphabet (Letter Q Z)} {halt q}
    (t : Tests A δ halt q) (x y : List Bool) (src : Computes δ halt q x y) :
    ∃ n, t.report (rounds n (seed (anchor A q x))) = some y := by
  obtain ⟨extra,us,vs,w,raw,hw,rows,probes,_⟩ := (accepted_iff_computes A δ halt q x y).mpr src
  obtain ⟨age,bp⟩ := (t.gateSpec us vs w hw).mpr probes
  have wp := (t.wordSpec _).mpr ⟨us,vs,w,raw,hw,rows⟩
  rw [← raw] at bp
  obtain ⟨n,z,hz⟩ := (first_output_domain t.wordTest t.bodyTest t.decode _).mpr ⟨extra,age,wp,bp⟩
  exact ⟨n,(computes_unique δ halt q (t.sound x z n hz) src) ▸ hz⟩

theorem Tests.output_iff {δ : Table Q (Symbol Z)} {A : Alphabet (Letter Q Z)} {halt q}
    (t : Tests A δ halt q) (x y : List Bool) :
    (∃ n, t.report (rounds n (seed (anchor A q x))) = some y) ↔ Computes δ halt q x y :=
  ⟨fun ⟨n,h⟩ => t.sound _ _ n h,t.complete _ _⟩

#print axioms Tests.output_iff
#print axioms Tests.regular_report
end TwoScans.Tableau.Certificate
