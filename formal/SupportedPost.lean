import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.EquivFin
import ShellAutomata

/- Replace an infinite presentation of a finite-control Post machine by its
actual finite subtype of reachable labels, preserving evaluation on every
input and every output. -/
set_option linter.style.haveILetI false
namespace TwoScans.SupportedPost
open Turing StateTransition
variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

@[instance_reducible] def start {M : TM0.Machine Γ Λ} {S : Finset Λ} (support : TM0.Supports M S) : Inhabited S :=
  ⟨⟨default, support.1⟩⟩

def restrict (M : TM0.Machine Γ Λ) (S : Finset Λ) (support : TM0.Supports M S) :
    @TM0.Machine Γ S (start support) :=
  fun q a => match h : M q.val a with
    | none => none
    | some (p,s) => some (⟨p,support.2 h q.property⟩,s)

def erase {S : Finset Λ} (c : TM0.Cfg Γ S) : TM0.Cfg Γ Λ := ⟨c.q.val,c.Tape⟩

theorem same_step (M : TM0.Machine Γ Λ) (S : Finset Λ) (support : TM0.Supports M S)
    (c : TM0.Cfg Γ S) :
    letI := start support
    TM0.step M (erase c) = (TM0.step (restrict M S support) c).map erase := by
  letI := start support
  rcases c with ⟨q,t⟩
  unfold TM0.step erase
  cases h : M q.val t.1 with
  | none => simp [restrict,h]; split <;> simp_all
  | some p =>
    rcases p with ⟨z,s⟩
    have mem := support.2 h q.property
    simp [restrict,h]; split <;> simp_all

theorem same_eval (M : TM0.Machine Γ Λ) (S : Finset Λ) (support : TM0.Supports M S) (l : List Γ) :
    letI := start support
    TM0.eval (restrict M S support) l = TM0.eval M l := by
  letI := start support
  let small := TM0.step (restrict M S support)
  have respects : Respects small (TM0.step M) (fun a b => erase a = b) := by
    apply fun_respects.mpr
    intro c
    cases e : small c with
    | none =>
      change TM0.step M (erase c) = none
      rw [same_step M S support]
      exact congrArg (Option.map erase) e
    | some d =>
      apply Relation.TransGen.single
      change TM0.step M (erase c) = some (erase d)
      rw [same_step M S support]
      exact congrArg (Option.map erase) e
  have h := tr_eval' small (TM0.step M) erase respects (TM0.init l)
  have initEq : erase (TM0.init l : TM0.Cfg Γ S) = (TM0.init l : TM0.Cfg Γ Λ) := rfl
  rw [initEq] at h
  unfold TM0.eval
  rw [h, Part.map_eq_map, Part.map_map]
  rfl

/-- Any Mathlib finite type provides the constructive finiteness witness for
the source alphabet, once a finite enumeration is chosen. -/
@[instance_reducible] noncomputable def finiteStates (A : Type) [Fintype A] : Automata.FinStates A :=
  let e := Fintype.equivFin A
  ⟨(List.finRange _).map e.symm, fun x => List.mem_map.mpr
      ⟨e x,List.mem_finRange _,e.symm_apply_apply x⟩⟩

#print axioms same_eval
end TwoScans.SupportedPost
