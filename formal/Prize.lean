import UniversalS
import BinaryInput

set_option linter.style.haveILetI false
namespace TwoScans.Prize
open Automata Frames Tableau Tableau.OneTape UniversalS StringCoding
open Turing

/-- Fix one universal machine once. These two operations on *raw bit strings*
construct its initial tape and the native pure-S seed by constant-size
replacements. In particular, creating the seed never evaluates a source program. -/
def encodeBits (P : Type) [FinStates P] [DecidableEq P] [Inhabited P]
    (p x : List Bool) : Term := by
  letI : DecidableEq UniversalPost.Cell := FiniteUniversalPost.cellDecEq
  exact AnyTape.startTerm FoldedTape.clear (FoldedTape.start (Λ := P) (BinaryInput.tape p x))

theorem agrees (P : Type) [FinStates P] [DecidableEq P] [Inhabited P] (c : Code) (x : List Bool) :
    encodeBits P (BinaryInput.program c) x = encodePost P c (pack x) := by
  simp only [encodeBits,encodePost,BinaryInput.source_tape]

def readStrings {P : Type} [FinStates P] [DecidableEq P] [Inhabited P]
    (M : TM0.Machine Cell P) (t : Term) := (readPost M t).map List.dropLast

/-- The witnesses use the structural bit encoder and the finite-table readout. -/
theorem universal_witness :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
      (M : @TM0.Machine Cell P st) (a b : Nat), letI := fp; letI := dp; letI := st
      Regular (fun t => ∃ y, readStrings M t = some y) ∧
      (∀ p x, size (encodeBits P p x) ≤ a+b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n, readStrings M (rounds n (encodeBits P p x)) = some y) ↔ y ∈ f x := by
  obtain ⟨P,fp,dp,hp,M,reg,allHits,graph⟩ := UniversalS.fixed_machine
  letI : FinStates P := fp
  letI : DecidableEq P := dp
  letI : Inhabited P := hp
  let E := encodeBits P
  let D := fun t => (readPost M t).map List.dropLast
  have regular : Regular (fun t => ∃ y, D t = some y) := by
    obtain ⟨Q,iq,fold,accept,h⟩ := reg
    refine ⟨Q,iq,fold,accept,fun t => ?_⟩
    rw [h]; cases e : readPost M t <;> simp [D,e]
  classical
  let s := (AnyTape.A (FoldedTape.Control P) (FoldedTape.Column UniversalPost.Cell)).width
  refine ⟨P,fp,dp,hp,M,2*size Shell.g+1+3*(6*s),3*s,regular,?_,?_⟩
  · intro p x
    change size (E p x) ≤ _
    let c := FoldedTape.start (Λ:=P) (BinaryInput.tape p x)
    have cap := AnyTape.size_start FoldedTape.clear c
    have dims := BinaryInput.folded_symbol_count (Q:=P) p x
    change c.left.length + 1 + c.right.length = _ at dims
    change size (E p x) ≤ 2*size Shell.g+1+3*((c.left.length+1+c.right.length+3)*s) at cap
    rw [dims] at cap
    apply cap.trans
    change 2*size Shell.g+1+3*((p.length+x.length+3+3)*s) ≤
      2*size Shell.g+1+3*(6*s)+3*s*(p.length+x.length)
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm]; omega
  · intro f hf
    obtain ⟨c,program⟩ := StringCoding.program hf
    refine ⟨BinaryInput.program c,fun x y => ?_⟩
    change (∃ n, (readPost M (rounds n (encodeBits P (BinaryInput.program c) x))).map List.dropLast = some y) ↔ _
    rw [agrees]
    constructor
    · rintro ⟨n,hn⟩
      obtain ⟨bits,hit,out⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨v,hv,rfl⟩ := allHits _ _ _ _ hit
      rw [program] at hv
      obtain ⟨str,hs,rfl⟩ := (Part.mem_map_iff _).mp hv
      have same : str = y := by simpa [binary_pack] using out
      exact same ▸ hs
    · intro hy
      have hv : pack y ∈ c.eval (pack x) := by rw [program]; exact (Part.mem_map_iff _).mpr ⟨y,hy,rfl⟩
      obtain ⟨n,h⟩ := (graph c (pack x) (pack y)).mpr hv
      exact ⟨n,by simp [h,binary_pack]⟩

/-- A single encoder, regular observation and readout for every library
partial recursive function on binary strings. Hit equivalence is a graph
equality, so it includes divergence and excludes *every* spurious output. -/
theorem universal_strings :
    ∃ (E : List Bool → List Bool → Term) (D : Term → Option (List Bool)) (a b : Nat),
      Regular (fun t => ∃ y, D t = some y) ∧
      (∀ p x, size (E p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n, D (rounds n (E p x)) = some y) ↔ y ∈ f x := by
  obtain ⟨P,fp,dp,hp,M,a,b,reg,cap,graph⟩ := universal_witness
  letI := fp; letI := dp; letI := hp
  exact ⟨encodeBits P,readStrings M,a,b,reg,cap,graph⟩

end TwoScans.Prize
#print axioms TwoScans.Prize.universal_strings
