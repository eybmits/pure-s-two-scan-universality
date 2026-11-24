import FiniteUniversalPost
import RowTapeRead
import TapeDecoder
import ShellAnyTape

/- From the universal Mathlib evaluator to the ground S trajectory, using
one fixed seed encoder, finite detector and output decoder on all codes. -/
set_option linter.style.haveILetI false
namespace TwoScans.UniversalS
open Turing Automata Tableau Tableau.OneTape FoldedTape UniversalPost
open Term Frames

abbrev Code := Nat.Partrec.Code
abbrev Cell := UniversalPost.Cell

variable {P : Type} [FinStates P] [DecidableEq P] [Inhabited P]
local instance : DecidableEq UniversalPost.Cell := FiniteUniversalPost.cellDecEq

private def running (M : TM0.Machine Cell P) :
    Table (Control P) (Column Cell) := FoldedTape.table M

private def stop (q : Control P) : Bool := q.1.isNone

def encodePost (P : Type) [FinStates P] [DecidableEq P] [Inhabited P] (c : Code) (x : Nat) :=
  AnyTape.startTerm (clear (Γ:=Cell)) (FoldedTape.start (Λ:=P) (tapeInput c x))

def readPost (M : TM0.Machine Cell P) (t : Term) : Option (List Bool) :=
  (AnyTape.report (running M) clear stop t).map (fun row => TapeDecoder.digits (rightOf row))

theorem regular_read (M : TM0.Machine Cell P) :
    Regular (fun t => ∃ y, readPost M t = some y) := by
  obtain ⟨Q,i,F,ok,h⟩ := AnyTape.report_regular (running M) clear stop
  refine ⟨Q,i,F,ok,fun t => ?_⟩; rw [h]
  unfold readPost
  cases AnyTape.report (running M) clear stop t <;> simp

theorem orbit_domain (M : TM0.Machine Cell P) (c : Code) (x : Nat) :
    (∃ j row, AnyTape.report (running M) clear stop (rounds j (encodePost P c x)) = some row) ↔
      (TM0.eval M (tapeInput c x)).Dom := by
  rw [encodePost,AnyTape.domain]
  constructor
  · rintro ⟨n,h⟩
    let z := ListBlank.mk (readCfg (run (advance (table M) clear) (FoldedTape.start (tapeInput c x)) n))
    have hz : z ∈ TM0.eval M (tapeInput c x) := (FoldedTape.output_iff M _ z).mpr ⟨n,h,rfl⟩
    exact hz.1
  · intro h
    obtain ⟨n,hn,_⟩ := (FoldedTape.output_iff M (tapeInput c x) _).mp ⟨h,rfl⟩
    exact ⟨n,hn⟩

theorem row_result (M : TM0.Machine Cell P)
    (domain : ∀ (c : Code) (x : Nat), (TM0.eval M (tapeInput c x)).Dom ↔ (c.eval x).Dom)
    (correct : ∀ (c : Code) (x y : Nat) (t : ListBlank Cell), y ∈ c.eval x → t ∈ TM0.eval M (tapeInput c x) → Outputs t y)
    (c : Code) (x j : Nat) (row : List (Color (Control P) (Column Cell)))
    (hit : AnyTape.report (running M) clear stop (rounds j (encodePost P c x)) = some row) :
    ∃ y ∈ c.eval x, TapeDecoder.digits (rightOf row) = TapeDecoder.binary y := by
  obtain ⟨n,k,halted,erow⟩ := AnyTape.sound (running M) clear stop _ j row hit
  let curr := run (advance (table M) clear) (FoldedTape.start (tapeInput c x)) n
  have hr : ListBlank.mk (rightOf row) = ListBlank.mk (readCfg curr) := by
    rw [erow,rightOf_padded]
    rfl
  have hz : ListBlank.mk (rightOf row) ∈ TM0.eval M (tapeInput c x) :=
    (FoldedTape.output_iff M _ _).mpr ⟨n,halted,hr.symm⟩
  have defined := (domain c x).mp hz.1
  let y := (c.eval x).get defined
  have ymem : y ∈ c.eval x := ⟨defined,rfl⟩
  obtain ⟨L,head,main⟩ := correct c x y _ ymem hz
  exact ⟨y,ymem,TapeDecoder.reads (rightOf row) L y head main⟩

/-- Uniformity over the entire library Gödel numbering. All outputs of the
actual decoder, at all times, have a unique defined source value. -/
theorem fixed_machine :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
        (M : @TM0.Machine Cell P st), letI := fp; letI := dp; letI := st
      Regular (fun t => ∃ y, readPost M t = some y) ∧
      (∀ (c : Code) x bits n, readPost M (rounds n (encodePost P c x)) = some bits →
        ∃ y ∈ c.eval x, bits = TapeDecoder.binary y) ∧
      (∀ (c : Code) x y, (∃ n, readPost M (rounds n (encodePost P c x)) = some (TapeDecoder.binary y)) ↔ y ∈ c.eval x) := by
  obtain ⟨P,fp,dp,q,M,domain,correct⟩ := FiniteUniversalPost.finite_universal
  letI : FinStates P := fp
  letI : DecidableEq P := dp
  letI : Inhabited P := ⟨q⟩
  have all c x bits n (hit : readPost M (rounds n (encodePost P c x)) = some bits) :
      ∃ y ∈ c.eval x, bits = TapeDecoder.binary y := by
    obtain ⟨row,found,rfl⟩ := Option.map_eq_some_iff.mp hit
    exact row_result M domain correct c x n row found
  refine ⟨P,fp,dp,⟨q⟩,M,regular_read M,all,?_⟩
  intro c x y
  constructor
  · rintro ⟨n,e⟩
    obtain ⟨v,hv,bits⟩ := all c x _ n e
    have eq := congrArg TapeDecoder.value bits
    simp only [TapeDecoder.binary_value] at eq
    simpa only [eq] using hv
  · intro hy
    obtain ⟨n,row,e⟩ := (orbit_domain M c x).mpr ((domain c x).mpr hy.1)
    obtain ⟨v,hv,out⟩ := row_result M domain correct c x n row e
    have eq := Part.mem_unique hv hy
    exact ⟨n,by simp [readPost,e,out,eq]⟩

theorem universal :
    ∃ (E : Code → Nat → Term) (D : Term → Option (List Bool)),
      Regular (fun t => ∃ y, D t = some y) ∧
      (∀ c x bits n, D (rounds n (E c x)) = some bits →
        ∃ y ∈ c.eval x, bits = TapeDecoder.binary y) ∧
      (∀ c x y, (∃ n, D (rounds n (E c x)) = some (TapeDecoder.binary y)) ↔ y ∈ c.eval x) := by
  obtain ⟨P,fp,dp,st,M,h⟩ := fixed_machine
  letI := fp; letI := dp; letI := st
  exact ⟨encodePost P,readPost M,h⟩

#print axioms fixed_machine
#print axioms universal
end TwoScans.UniversalS
