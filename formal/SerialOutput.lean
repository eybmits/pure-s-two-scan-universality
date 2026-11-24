import Prize
import SerialReadout

namespace TwoScans.Prize
open Automata Frames SerialReadout SerialTableau

/-- Follow one fixed sequence of actual one-redex contractions. A run stops
    at its first simultaneous hit on the two tracked copies. Searching finite
    prefixes makes the first-hit convention precise even for divergent inputs. -/
theorem serial_universal_strings :
    ∃ (E : List Bool → List Bool → Term) (D : Term → Option (List Bool)) (a b : Nat),
      Regular (fun t => ∃ y, D t = some y) ∧
      (∀ p x, size (E p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n, readFirst D (E p x) n = some y) ↔ y ∈ f x := by
  obtain ⟨E,D,a,b,reg,cap,works⟩ := universal_strings
  refine ⟨fun p x => pack (E p x) (E p x),double D,1+2*a,2*b,regular_double _ reg,?_,?_⟩
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

end TwoScans.Prize
#print axioms TwoScans.Prize.serial_universal_strings
