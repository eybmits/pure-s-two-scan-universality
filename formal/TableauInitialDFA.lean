import MachineAlphabet
import ShellStatic

namespace TwoScans.Tableau.OneTape
open Automata Static
variable {Q Z : Type}

inductive InputState | empty | padding | bits | valid | invalid deriving DecidableEq,Repr,Inhabited
instance : FinStates InputState := ⟨[.empty,.padding,.bits,.valid,.invalid],fun s => by cases s <;> simp⟩

def inputStep [DecidableEq Q] (q : Q) : Cell Q Z → InputState → InputState
  | .wall, .empty => .padding
  | .plain .blank, .padding => .padding
  | .plain .inputEnd, .padding => .bits
  | .plain (.bit _), .bits => .bits
  | .head p .start, .bits => if p = q then .valid else .invalid
  | _, _ => .invalid

def inputAccept (s : InputState) : Bool := decide (s = .valid)

private def blanks (k : Nat) : List (Cell Q Z) := List.replicate k (.plain .blank) ++ [.wall]
private def body (x : List Bool) (k : Nat) : List (Cell Q Z) :=
  x.map (fun b => .plain (.bit b)) ++ (.plain .inputEnd :: blanks k)
private theorem encoded_initial (q : Q) (x : List Bool) (k : Nat) :
    encode (pad (.blank : Symbol Z) (initial q x) k) = .head q .start :: body x k := by
  simp [encode,pad,initial,body,blanks,List.map_map,Function.comp_def,List.append_assoc]

private def invariant (q : Q) (row : List (Cell Q Z)) : InputState → Prop
  | .empty => row = []
  | .padding => ∃ k, row = blanks k
  | .bits => ∃ x k, row = body x k
  | .valid => ∃ x k, row = encode (pad .blank (initial q x) k)
  | .invalid => True

private theorem invariant_preserved [DecidableEq Q] (q : Q) (c : Cell Q Z) (r)
    (s : InputState) (h : invariant q r s) : invariant q (c::r) (inputStep q c s) := by
  cases c with
  | wall =>
    cases s <;> try trivial
    exact ⟨0,by rw [show r = [] from h]; rfl⟩
  | plain a =>
    cases a <;> cases s <;> try trivial
    case bit.bits b =>
      obtain ⟨x,k,e⟩ := h
      exact ⟨b::x,k,by rw [e]; rfl⟩
    case inputEnd.padding =>
      obtain ⟨k,e⟩ := h
      exact ⟨[],k,by rw [e]; rfl⟩
    case blank.padding =>
      obtain ⟨k,e⟩ := h
      exact ⟨k+1,by rw [e]; simp [blanks,List.replicate_succ]⟩
  | head p a =>
    cases a <;> cases s <;> try trivial
    case start.bits =>
      obtain ⟨x,k,e⟩ := h
      by_cases hp : p=q
      · subst p
        simp only [inputStep, ↓reduceIte, invariant]
        exact ⟨x,k,by rw [e,encoded_initial]⟩
      · simp [inputStep,hp,invariant]

private theorem blanks_fold [DecidableEq Q] (q : Q) (k : Nat) :
    (blanks (Q:=Q) (Z:=Z) k).foldr (inputStep q) .empty = .padding := by
  induction k with
  | zero => rfl
  | succ k ih => change inputStep q (.plain .blank) ((blanks k).foldr _ _) = _; rw [ih]; rfl

private theorem body_fold [DecidableEq Q] (q : Q) (x : List Bool) (k : Nat) :
    (body (Q:=Q) (Z:=Z) x k).foldr (inputStep q) .empty = .bits := by
  induction x with
  | nil => change inputStep q (.plain .inputEnd) ((blanks k).foldr _ _) = _; rw [blanks_fold]; rfl
  | cons b x ih => change inputStep q (.plain (.bit b)) ((body x k).foldr _ _) = _; rw [ih]; rfl

theorem input_iff [DecidableEq Q] (q : Q) (r : List (Cell Q Z)) :
    inputAccept (r.foldr (inputStep q) .empty) = true ↔
    ∃ x k, r = encode (pad .blank (initial q x) k) := by
  constructor
  · intro h
    have inv : invariant q r (r.foldr (inputStep q) .empty) := by
      clear h
      induction r with
      | nil => rfl
      | cons c r ih => exact invariant_preserved _ _ _ _ ih
    have eq : r.foldr (inputStep q) .empty = .valid := of_decide_eq_true h
    rw [eq] at inv
    exact inv
  · rintro ⟨x,k,rfl⟩
    rw [encoded_initial,List.foldr_cons,body_fold]
    simp [inputStep,inputAccept]

#print axioms input_iff
end TwoScans.Tableau.OneTape
