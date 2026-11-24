import Prize
import ReadPostBound
import OutputPreimage

set_option linter.style.haveILetI false
namespace TwoScans.Certified
open Automata Frames Tableau Tableau.OneTape UniversalS Prize Turing

/-- A fixed finite table supplies both witnesses. Its ground seed has linear size.
Any regular test on the returned string is a regular test on the raw S tree.
The domain, output-size bound, and graph cover the very same decoder. -/
theorem universality :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
      (M : @TM0.Machine Cell P st) (a b : Nat), letI := fp; letI := dp; letI := st
      Regular (fun t => ∃ y, readStrings M t = some y) ∧
      (∀ q : List Bool → Bool, WordRead.Attr q →
        Regular (fun t => ∃ y, readStrings M t = some y ∧ q y = true)) ∧
      (∀ t y, readStrings M t = some y → y.length ≤ 2 * size t) ∧
      (∀ p x, size (encodeBits P p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n, readStrings M (rounds n (encodeBits P p x)) = some y) ↔ y ∈ f x := by
  obtain ⟨P,fp,dp,st,M,a,b,reg,cap,graph⟩ := universal_witness
  letI := fp; letI := dp; letI := st
  refine ⟨P,fp,dp,st,M,a,b,reg,OutputPreimage.regular M,?_,cap,graph⟩
  intro t y hit
  obtain ⟨bits,h,rfl⟩ := Option.map_eq_some_iff.mp hit
  have bound := readPost_length M t bits h
  simp only [List.length_dropLast]
  omega

end TwoScans.Certified
#print axioms TwoScans.Certified.universality
