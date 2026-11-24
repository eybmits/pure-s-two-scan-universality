import ShellWordAutomata
import WordBlocks

namespace TwoScans.Language
open Automata WordBlocks

/-- A deterministic finite automaton reading a word from its end. -/
def Reg {α : Type} (P : List α → Prop) := ∃ (Q : Type) (_ : FinStates Q) (q : Q)
    (d : α → Q → Q) (accept : Q → Bool), ∀ w, accept (w.foldr d q) = true ↔ P w

def cat {α : Type} (P R : List α → Prop) (w : List α) :=
  ∃ u v, w = u ++ v ∧ P u ∧ R v

theorem congruence {α} {P R : List α → Prop} (hp : Reg P) (e : ∀ w, P w ↔ R w) : Reg R := by
  obtain ⟨Q,i,q,d,a,h⟩ := hp
  exact ⟨Q,i,q,d,a,fun w => (h w).trans (e w)⟩

theorem emptyWord (α : Type) : Reg (fun w : List α => w = []) :=
  ⟨Bool,inferInstance,true,(fun _ _ => false),id,fun w => by cases w <;> simp⟩

theorem single {α : Type} [DecidableEq α] (x : α) : Reg (fun w => w = [x]) := by
  let d (b : α) (q : Option Bool) := match q with | none => some (decide (b=x)) | some _ => some false
  have n (w : List α) : w.foldr d none = none ↔ w = [] := by
    cases w with
    | nil => simp
    | cons b w => simp only [List.foldr_cons]; cases w.foldr d none <;> simp [d]
  refine ⟨Option Bool,inferInstance,none,d,(fun z => z.getD false),?_⟩
  intro w
  cases w with
  | nil => simp
  | cons b w =>
    simp only [List.foldr_cons]
    cases e : w.foldr d none with
    | none => have z := (n w).1 e; simp [d,z]
    | some z => have h : w ≠ [] := by intro he; subst w; cases e
                simp [d,h]

theorem concatenate {α : Type} {P R : List α → Prop} (hp : Reg P) (hr : Reg R) :
    Reg (cat P R) := by
  classical
  obtain ⟨A,ia,qa,da,pa,ha⟩ := hp
  obtain ⟨B,ib,qb,db,pb,hb⟩ := hr
  haveI := ia
  haveI := ib
  let d (b : α) (z : B × (A → Bool)) : B × (A → Bool) :=
    (db b z.1,fun x => (decide (x = qa) && pb (db b z.1)) ||
      (FinStates.enum (Q:=A)).any (fun y => z.2 y && decide (da b y = x)))
  let init : B × (A → Bool) := (qb,fun x => decide (x = qa) && pb qb)
  have spec (w : List α) : (w.foldr d init).1 = w.foldr db qb ∧
      ∀ x, (w.foldr d init).2 x = true ↔
        ∃ u v, w = u ++ v ∧ u.foldr da qa = x ∧ R v := by
    induction w with
    | nil =>
      refine ⟨rfl,fun x => ?_⟩
      simp only [List.foldr_nil,init,Bool.and_eq_true,decide_eq_true_eq]
      change (x = qa ∧ pb ([].foldr db qb) = true) ↔ _
      rw [hb]
      constructor
      · rintro ⟨rfl,h⟩; exact ⟨[],[],rfl,rfl,h⟩
      · rintro ⟨u,v,e,hu,hv⟩; cases u <;> cases e; exact ⟨hu.symm,hv⟩
    | cons b w ih =>
      refine ⟨by simp only [List.foldr_cons,d,ih.1],fun x => ?_⟩
      simp only [List.foldr_cons,d,Bool.or_eq_true,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq]
      rw [ih.1,show db b (w.foldr db qb) = (b::w).foldr db qb from rfl,hb]
      constructor
      · rintro (⟨rfl,rv⟩ | ⟨y,_,hy,ex⟩)
        · exact ⟨[],b::w,rfl,rfl,rv⟩
        · obtain ⟨u,v,rfl,hu,hv⟩ := (ih.2 y).mp hy
          exact ⟨b::u,v,rfl,by rw [List.foldr_cons,hu,ex],hv⟩
      · rintro ⟨u,v,e,hu,hv⟩
        cases u with
        | nil => cases e; exact .inl ⟨hu.symm,hv⟩
        | cons c u =>
          cases e
          exact .inr ⟨_,FinStates.covers _,(ih.2 _).2 ⟨u,v,rfl,rfl,hv⟩,hu⟩
  let accept (s : B × (A → Bool)) := FinStates.enum.any (fun x => s.2 x && pa x)
  refine ⟨_,inferInstance,init,d,accept,?_⟩
  intro w
  simp only [accept,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨x,_,hx,ok⟩
    obtain ⟨u,v,e,hu,hv⟩ := ((spec w).2 x).mp hx
    exact ⟨u,v,e,(ha u).mp (hu ▸ ok),hv⟩
  · rintro ⟨u,v,e,hu,hv⟩
    exact ⟨_,FinStates.covers _,((spec w).2 _).mpr ⟨u,v,e,rfl,hv⟩,(ha u).mpr hu⟩

theorem exactWord {α : Type} [DecidableEq α] (v : List α) : Reg (· = v) := by
  induction v with
  | nil => exact emptyWord α
  | cons a v ih =>
    apply congruence (concatenate (single a) ih)
    intro w
    constructor
    · rintro ⟨_,_,e,rfl,rfl⟩; exact e
    · intro e; exact ⟨[a],v,e,rfl,rfl⟩

/-- Lift a word language through an injective letter tagging operation. -/
theorem mapped {α β : Type} {P : List α → Prop} (wrap : α → β) (get : β → Option α)
    (inv : ∀ b a, get b = some a ↔ b = wrap a) (hp : Reg P) :
    Reg (fun w => ∃ u, w = u.map wrap ∧ P u) := by
  obtain ⟨Q,iq,q,d,a,h⟩ := hp
  haveI := iq
  let step (b : β) (acc : Option Q) := (get b).bind (fun c => acc.map (d c))
  have eval (xs : List α) : (xs.map wrap).foldr step (some q) = some (xs.foldr d q) := by
    induction xs with
    | nil => rfl
    | cons b xs ih => simp [step,ih,(inv (wrap b) b).mpr rfl]
  have decomp (w : List β) (z : Q) (ok : w.foldr step (some q) = some z) :
      ∃ u : List α, w = u.map wrap ∧ u.foldr d q = z := by
    induction w generalizing z with
    | nil => cases ok; exact ⟨[],rfl,rfl⟩
    | cons b w ih =>
      change (get b).bind (fun c => (w.foldr step (some q)).map (d c)) = some z at ok
      cases eb : get b with
      | none => simp [eb] at ok
      | some c =>
        cases ev : w.foldr step (some q) with
        | none => simp [eb,ev] at ok
        | some x =>
          have wk := (inv _ _).mp eb
          obtain ⟨u,rfl,eu⟩ := ih _ ev
          simp only [eb,Option.bind_some,ev,Option.map_some,Option.some.injEq] at ok
          exact ⟨c::u,by rw [wk]; rfl,by rw [List.foldr_cons,eu,ok]⟩
  refine ⟨Option Q,inferInstance,some q,step,fun v => v.elim false a,?_⟩
  intro w; constructor
  · cases ew : w.foldr step (some q) with
    | none => intro ok; cases ok
    | some z =>
      intro ok
      obtain ⟨u,rfl,rfl⟩ := decomp w z ew
      exact ⟨u,rfl,(h u).mp ok⟩
  · rintro ⟨u,rfl,ok⟩; rw [eval]; exact (h u).mpr ok

theorem unrestricted (α : Type) : Reg (fun _ : List α => True) :=
  ⟨Unit,inferInstance,(),fun _ _ => (),fun _ => true,fun _ => by simp⟩
end TwoScans.Language
