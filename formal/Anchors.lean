import Std

namespace TwoScans

inductive Term where
  | s
  | app (left right : Term)
  deriving DecidableEq

open Term

inductive Occ (a : Term) : Term → Prop where
  | here : Occ a a
  | left {l r} : Occ a l → Occ a (app l r)
  | right {l r} : Occ a r → Occ a (app l r)

inductive Step : Term → Term → Prop where
  | root (x y z : Term) :
      Step (app (app (app s x) y) z) (app (app x z) (app y z))
  | left {a b} (r : Term) : Step a b → Step (app a r) (app b r)
  | right {a b} (l : Term) : Step a b → Step (app l a) (app l b)

def Normal (a : Term) := ∀ b, ¬ Step a b

theorem Occ.trans {a b c : Term} (hab : Occ a b) (hbc : Occ b c) : Occ a c := by
  induction hbc with
  | here => exact hab
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem Normal.sub {a b : Term} (hb : Normal b) (hab : Occ a b) : Normal a := by
  induction hab with
  | here => exact hb
  | left h ih => exact ih (fun _ step => hb _ (.left _ step))
  | right h ih => exact ih (fun _ step => hb _ (.right _ step))

inductive Safe (l v : Term) : Term → Prop where
  | origL {a} : Occ a l → Safe l v a
  | origR {a} : Occ a v → Safe l v a
  | join {a b} : Safe l v a → Safe l v b → Occ v b → Safe l v (app a b)

namespace Safe

theorem children {l v a b} (h : Safe l v (app a b)) : Safe l v a ∧ Safe l v b := by
  cases h with
  | origL h => exact ⟨.origL ((Occ.left Occ.here).trans h), .origL ((Occ.right Occ.here).trans h)⟩
  | origR h => exact ⟨.origR ((Occ.left Occ.here).trans h), .origR ((Occ.right Occ.here).trans h)⟩
  | join ha hb _ => exact ⟨ha, hb⟩

theorem sub {l v a b} (h : Safe l v b) (o : Occ a b) : Safe l v a := by
  induction o with
  | here => exact h
  | left _ ih => exact ih h.children.1
  | right _ ih => exact ih h.children.2

theorem cut {l v a b t} (hl : Normal l) (hv : Normal v)
    (h : Safe l v (app a b)) (st : Step (app a b) t) : Occ v b := by
  cases h with
  | origL h => exact False.elim ((hl.sub h) _ st)
  | origR h => exact False.elim ((hv.sub h) _ st)
  | join _ _ inside => exact inside

theorem one {l v a b} (hl : Normal l) (hv : Normal v) (st : Step a b)
    (h : Safe l v a) : Safe l v b ∧ (Occ v a → Occ v b) := by
  induction st with
  | root x y z =>
    have iz := cut hl hv h (.root x y z)
    have hxy := h.children
    have hsy := hxy.1.children
    have hx := hsy.1.children.2
    have xz := Safe.join hx hxy.2 iz
    have yz := Safe.join hsy.2 hxy.2 iz
    exact ⟨.join xz yz (.right iz), fun _ => .left (.right iz)⟩
  | left r st ih =>
    have ir := cut hl hv h (.left r st)
    have next := ih h.children.1
    exact ⟨.join next.1 h.children.2 ir, fun _ => .right ir⟩
  | right f st ih =>
    have ir := cut hl hv h (.right f st)
    have next := ih h.children.2
    have kept := next.2 ir
    exact ⟨.join h.children.1 next.1 kept, fun _ => .right kept⟩

end Safe

inductive Steps : Term → Term → Prop where
  | refl (t) : Steps t t
  | tail {a b c} : Steps a b → Step b c → Steps a c

theorem keepsSafe {l v t u} (hl : Normal l) (hv : Normal v) (hs : Safe l v t)
    (steps : Steps t u) : Safe l v u := by
  induction steps with
  | refl => exact hs
  | tail _ st ih => exact (Safe.one hl hv st ih).1

/-- Every application in any reduct of two normal operands is original,
    or its right child still contains the entire original argument. -/
theorem intactAnchor {l v t a b} (hl : Normal l) (hv : Normal v)
    (steps : Steps (app l v) t) (node : Occ (app a b) t) :
    Occ (app a b) l ∨ Occ (app a b) v ∨ Occ v b := by
  have initial : Safe l v (app l v) := .join (.origL .here) (.origR .here) .here
  cases (keepsSafe hl hv initial steps).sub node with
  | origL h => exact Or.inl h
  | origR h => exact Or.inr (Or.inl h)
  | join _ _ h => exact Or.inr (Or.inr h)

def size : Term → Nat
  | s => 1
  | app a b => size a + size b

theorem sizePos (t : Term) : 0 < size t := by
  induction t with
  | s => decide
  | app a b ha hb => simp only [size]; omega

theorem sizeStep {a b} (st : Step a b) : size a ≤ size b := by
  induction st with
  | root x y z => have hz := sizePos z; simp only [size]; omega
  | left r _ ih => simp only [size]; omega
  | right l _ ih => simp only [size]; omega

/-- Guard at every application, including ancestors of the active redex. -/
inductive Guard (k : Nat) : Term → Prop where
  | leaf : Guard k s
  | node {a b} : Guard k a → Guard k b →
      (∀ u, Step (app a b) u → k < size b) → Guard k (app a b)

namespace Guard

theorem parts {k a b} (h : Guard k (app a b)) : Guard k a ∧ Guard k b := by
  cases h with | node ha hb _ => exact ⟨ha, hb⟩

theorem bound {k a b u} (h : Guard k (app a b)) (st : Step (app a b) u) :
    k < size b := by
  cases h with | node _ _ h => exact h _ st

theorem sub {k a b} (h : Guard k b) (o : Occ a b) : Guard k a := by
  induction o with
  | here => exact h
  | left _ ih => exact ih h.parts.1
  | right _ ih => exact ih h.parts.2

theorem step {k a b} (st : Step a b) (h : Guard k a) : Guard k b := by
  induction st with
  | root x y z =>
    have hz := h.bound (.root x y z)
    have hx := h.parts.1.parts.1.parts.2
    have hy := h.parts.1.parts.2
    have hgz := h.parts.2
    exact .node (.node hx hgz (fun _ _ => hz)) (.node hy hgz (fun _ _ => hz))
        (fun _ _ => by simp only [size]; omega)
  | left r st ih =>
    have old := h.bound (.left r st)
    exact .node (ih h.parts.1) h.parts.2 (fun _ _ => old)
  | right f st ih =>
    have old := h.bound (.right f st)
    have mono := sizeStep st
    exact .node h.parts.1 (ih h.parts.2) (fun _ _ => by omega)

theorem steps {k a b} (sts : Steps a b) (h : Guard k a) : Guard k b := by
  induction sts with
  | refl => exact h
  | tail _ st ih => exact step st ih

end Guard

/-- From a guarded scanner state, no future redex can have a small right operand. -/
theorem noLateShortCall {k a b f z u} (h : Guard k a) (sts : Steps a b)
    (o : Occ (app f z) b) (hz : size z ≤ k) : ¬Step (app f z) u := by
  intro st
  have hbig := ((Guard.steps sts h).sub o).bound st
  omega

#print axioms intactAnchor
#print axioms noLateShortCall

end TwoScans
