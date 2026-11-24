import ShellAutomata

namespace TwoScans.WordRead
open Automata

/-- A word summary computable by a finite right-to-left word automaton. -/
def Attr {α V : Type} (f : List α → V) :=
  ∃ (Q : Type) (_ : FinStates Q) (start : Q) (step : α → Q → Q) (out : Q → V),
    ∀ w, out (w.foldr step start) = f w

/-- A left-to-right pass is also a right-to-left finite summary: each
suffix stores its action on every possible incoming state. -/
theorem ofFoldl {α Q V : Type} [FinStates Q] (q : Q) (step : Q → α → Q)
    (out : Q → V) : Attr (fun w => out (w.foldl step q)) := by
  classical
  letI : Inhabited Q := ⟨q⟩
  let update := fun a (k : Q → Q) (s : Q) => k (step s a)
  have eq (w : List α) (s : Q) : (w.foldr update id) s = w.foldl step s := by
    induction w generalizing s with
    | nil => rfl
    | cons a w ih => exact ih _
  exact ⟨Q → Q,inferInstance,id,update,(fun k => out (k q)),fun w => congrArg out (eq w q)⟩

theorem map {α V W : Type} {f : List α → V} (h : Attr f) (g : V → W) :
    Attr (fun w => g (f w)) := by
  obtain ⟨Q,i,q,s,o,e⟩ := h
  exact ⟨Q,i,q,s,g ∘ o,fun w => congrArg g (e w)⟩

/-- Each prescribed output bit, including existence at that index, is a
finite-state word observation. -/
theorem bit_attr (i : Nat) (b : Bool) : Attr (fun w : List Bool => w[i]? == some b) := by
  induction i with
  | zero =>
    exact ⟨Bool,inferInstance,false,fun a _ => a == b,id,fun w => by
      cases w with | nil => rfl | cons a r => cases a <;> cases b <;> rfl⟩
  | succ i ih =>
    obtain ⟨Q,iq,q,s,out,h⟩ := ih
    haveI := iq
    let upd := fun a (z : Q × Bool) => (s a z.1,out z.1)
    have eq (w : List Bool) : (w.foldr upd (q,false)).1 = w.foldr s q := by
      induction w with | nil => rfl | cons a w ih => exact congrArg (s a) ih
    refine ⟨Q × Bool,inferInstance,(q,false),upd,Prod.snd,fun w => ?_⟩
    cases w with
    | nil => rfl
    | cons a w => exact (congrArg out (eq w)).trans (h w)

theorem exact_attr {α : Type} [DecidableEq α] (v : List α) :
    Attr (fun w => decide (w = v)) := by
  induction v with
  | nil =>
    exact ⟨Bool,inferInstance,true,fun _ _ => false,id,fun w => by cases w <;> rfl⟩
  | cons a v ih =>
    obtain ⟨Q,iq,q,s,out,h⟩ := ih
    haveI := iq
    let upd := fun b (z : Q × Bool) => (s b z.1,decide (b = a) && out z.1)
    have eq (w : List α) : (w.foldr upd (q,false)).1 = w.foldr s q := by
      induction w with | nil => rfl | cons b w ih => exact congrArg (s b) ih
    refine ⟨Q × Bool,inferInstance,(q,false),upd,Prod.snd,fun w => ?_⟩
    cases w with
    | nil => rfl
    | cons b w =>
      change (decide (b = a) && out (w.foldr upd (q,false)).1) = _
      simp [eq,h]

end TwoScans.WordRead
