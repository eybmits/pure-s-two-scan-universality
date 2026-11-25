import Certified
import SerialReadout

namespace TwoScans.Prize
open Automata Frames SerialReadout SerialTableau UniversalS
set_option linter.style.haveILetI false

/-- First detection along the fixed single-contraction sweep, using two copies
    of the structural bit seed and the double reader for one finite machine.
    Every regular output query has a regular preimage on all raw snapshots. -/
theorem serial_universal_witness :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
      (M : @Turing.TM0.Machine Cell P st) (a b : Nat), letI := fp; letI := dp; letI := st
      let E := encodeBits P
      let D := readStrings M
      let start := fun p x => pack (E p x) (E p x)
      Regular (fun t => ∃ y, double D t = some y) ∧
      (∀ q : List Bool → Bool, WordRead.Attr q →
        Regular (fun t => ∃ y, double D t = some y ∧ q y = true)) ∧
      (∀ p x, size (start p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n, readFirst (double D) (start p x) n = some y) ↔ y ∈ f x := by
  obtain ⟨P,fp,dp,st,M,a,b,reg,pre,_,cap,works⟩ := Certified.universality
  letI := fp; letI := dp; letI := st
  let E := encodeBits P
  let D := readStrings M
  refine ⟨P,fp,dp,st,M,1+2*a,2*b,regular_double D reg,?_,?_,?_⟩
  · intro q hq; exact regular_double_query D (fun y => q y = true) reg (pre q hq)
  · intro p x
    have le := cap p x
    simp only [pack,size,Nat.mul_assoc]
    omega
  · intro f hf
    obtain ⟨p,hp⟩ := works f hf
    refine ⟨p,fun x y => ?_⟩
    constructor
    · rintro ⟨n,hy⟩
      exact (hp x y).mp (first_from_parallel D (E p x) n hy)
    · intro hy
      obtain ⟨j,hit⟩ := (hp x y).mpr hy
      obtain ⟨z,serial⟩ := parallel_has_first D (E p x) j hit
      have hz := (hp x z).mp (first_from_parallel D (E p x) j serial)
      have eq : z = y := Part.mem_unique hz hy
      exact ⟨j,eq ▸ serial⟩

/-- Existential interface obtained by forgetting the explicit witnesses. -/
theorem serial_universal_strings :
    ∃ (E : List Bool → List Bool → Term) (D : Term → Option (List Bool)) (a b : Nat),
      Regular (fun t => ∃ y, D t = some y) ∧
      (∀ p x, size (E p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n, readFirst D (E p x) n = some y) ↔ y ∈ f x := by
  obtain ⟨P,fp,dp,st,M,a,b,reg,_,cap,graph⟩ := serial_universal_witness
  letI := fp; letI := dp; letI := st
  exact ⟨fun p x => pack (encodeBits P p x) (encodeBits P p x),
    double (readStrings M),a,b,reg,cap,graph⟩

end TwoScans.Prize
#print axioms TwoScans.Prize.serial_universal_witness
