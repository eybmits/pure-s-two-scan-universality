import RowTapeRead
import TapeDecoder
import WordRead

set_option linter.style.haveILetI false
namespace TwoScans.RowFinite
open FoldedTape Tableau.OneTape Automata WordRead

variable {Γ Λ X : Type}
abbrev Row (Λ Γ : Type) := List (Color (Control Λ) (Column Γ))
private abbrev E (X : Type) := X → X
private abbrev Status (X : Type) := E X × ((E X × E X) → X)

/-- The first table summarizes positive symbols in the tail. The second
uses the two incoming prefix actions to evaluate the first head. -/
private def push (s : X → Γ → X) (base : X) (tile : Color (Control Λ) (Column Γ))
    (r : Status X) : Status X := match tile with
  | .wall => (r.1,fun _ => base)
  | .plain a => (fun x => r.1 (s x a.2.1),fun p =>
      r.2 (fun x => s (p.1 x) a.2.1, fun x => p.2 (s x a.2.2)))
  | .head q a => (r.1,fun p => r.1 (s (if q.2 then base else p.1 (p.2 (s base a.2.2))) a.2.1))

private def tailPos (w : Row Λ Γ) := (w.filterMap plain?).map (fun a => a.2.1)
private def posPrefix (a : List (Column Γ)) := a.reverse.map (fun t => t.2.1)
private def negPrefix (a : List (Column Γ)) := a.map (fun t => t.2.2)
private def fromAcc (acc : List (Column Γ)) (w : Row Λ Γ) :=
  match parseRow acc w with | none => [] | some c => readCfg c

private theorem summarizes (s : X → Γ → X) (base : X) (w : Row Λ Γ) :
    let r := w.foldr (push s base) (id,fun _ => base)
    (∀ x, r.1 x = (tailPos w).foldl s x) ∧
    (∀ a : List (Column Γ), r.2 (fun x => (posPrefix a).foldl s x,
      fun x => (negPrefix a).foldl s x) = (fromAcc a w).foldl s base) := by
  induction w with
  | nil => exact ⟨fun _ => rfl,fun _ => rfl⟩
  | cons tile w ih =>
    rcases ih with ⟨tail,head⟩
    dsimp only
    cases tile with
    | wall => exact ⟨tail,fun _ => rfl⟩
    | plain a =>
      refine ⟨fun x => tail _,fun acc => ?_⟩
      change _ = (fromAcc (a :: acc) w).foldl s base
      rw [←head]
      simp [push,posPrefix,negPrefix,List.foldl_append]
    | head q a =>
      refine ⟨tail,fun acc => ?_⟩
      cases q with | mk q side =>
        cases side <;> simp [push,tail,fromAcc,parseRow,readCfg,unpack,rightList,
          posPrefix,negPrefix,tailPos,List.map_map,Function.comp_def,List.foldl_append]

/-- Pull back any finite left-to-right tape calculation through the
actual row reader, including malformed rows and either folded track. -/
theorem rightOf_attr [FinStates X] (s : X → Γ → X) (base : X) :
    Attr (fun w : Row Λ Γ => (rightOf w).foldl s base) := by
  classical
  letI : Inhabited X := ⟨base⟩
  exact ⟨Status X,inferInstance,(id,fun _ => base),push s base,fun r => r.2 (id,id),
    fun w => (summarizes s base w).2 []⟩

private def digit (a : TapeDecoder.Cell) := (a.2 Turing.PartrecToTM2.K'.main).bind TapeDecoder.bit?
private def emit (step : Bool → X → X) (z : Bool × X) (a : TapeDecoder.Cell) : Bool × X :=
  match digit a with
  | none => z
  | some b => (true, if z.1 then step b z.2 else z.2)

private theorem emitted (step : Bool → X → X) (r : List TapeDecoder.Cell) (x : X) (seen : Bool) :
    (r.foldl (emit step) (seen,x)).2 =
    (if seen then r.filterMap digit else (r.filterMap digit).tail).foldl (fun q b => step b q) x := by
  induction r generalizing seen x with
  | nil => cases seen <;> rfl
  | cons a r ih =>
    cases e : digit a with
    | none => simpa [emit,e] using ih x seen
    | some b => cases seen <;> simp [emit,e,ih]

/-- Any finite-state output predicate pulls back along the full row decoder,
including digit selection, orientation reversal, and removal of the sentinel. -/
theorem read_attr [FinStates X] (step : Bool → X → X) (base : X) (accept : X → Bool) :
    Attr (fun w : Row Λ TapeDecoder.Cell =>
      accept (((TapeDecoder.digits (rightOf w)).dropLast).foldr step base)) := by
  have h := WordRead.map (rightOf_attr (Λ:=Λ) (emit step) (false,base)) (fun z => accept z.2)
  convert h using 1
  funext w
  simp only [emitted,Bool.false_eq_true,ite_false,TapeDecoder.digits,List.dropLast_reverse,List.foldr_reverse]
  rfl

end TwoScans.RowFinite
#print axioms TwoScans.RowFinite.read_attr
