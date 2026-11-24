import ObserverPacket
import ShellAutomata

namespace TwoScans.Observer
open Term Frames Scan Generation Live Automata

/-- A finite-valued attribute with an explicit bottom-up finite-state implementation. -/
def Attribute {V : Type} (f : Term → V) : Prop :=
  ∃ (Q : Type) (_ : FinStates Q) (a : Fold Q) (out : Q → V), ∀ t, out (a.run t) = f t

theorem attrMap {A B : Type} {f : Term → A} (hf : Attribute f) (g : A → B) :
    Attribute (fun t => g (f t)) := by
  obtain ⟨Q,inst,a,o,h⟩ := hf
  exact ⟨Q,inst,a,g ∘ o,fun t => congrArg g (h t)⟩

theorem attrPair {A B : Type} {f : Term → A} {g : Term → B}
    (hf : Attribute f) (hg : Attribute g) : Attribute (fun t => (f t,g t)) := by
  obtain ⟨Q,iq,a,o,ha⟩ := hf
  obtain ⟨R,ir,b,u,hb⟩ := hg
  let ab : Fold (Q × R) := ⟨(a.leaf,b.leaf),fun l r => (a.fork l.1 r.1,b.fork l.2 r.2)⟩
  have h (t) : ab.run t = (a.run t,b.run t) := by
    induction t with
    | s => rfl
    | app l r hl hr => simp [Fold.run,hl,hr,ab]
  exact ⟨Q × R,inferInstance,ab,fun x => (o x.1,u x.2),fun t => by rw [h]; simp [ha,hb]⟩

/-- Compile a recursively accumulated finite result, with finite child attributes. -/
private theorem attrRec {A B : Type} [FinStates B] {f : Term → A} {g : Term → B}
    (hf : Attribute f) (z : B) (op : A → A → B → B → B) (hs : g s = z)
    (hb : ∀ l r, g (l ⋆ r) = op (f l) (f r) (g l) (g r)) : Attribute g := by
  obtain ⟨Q,iq,a,o,ha⟩ := hf
  let ab : Fold (Q × B) := ⟨(a.leaf,z),fun l r => (a.fork l.1 r.1,op (o l.1) (o r.1) l.2 r.2)⟩
  have h (t) : ab.run t = (a.run t,g t) := by
    induction t with
    | s => simp [Fold.run,ab,hs]
    | app l r hl hr => simp [Fold.run,hl,hr,ab,ha,hb]
  exact ⟨Q × B,inferInstance,ab,Prod.snd,fun t => by rw [h]⟩

private def constant (_t : Term) := false
private theorem attrConst : Attribute constant := ⟨Bool,inferInstance,⟨false,fun _ _ => false⟩,fun _ => false,fun _ => rfl⟩

def node {A B : Type} (f : Term → A) (z : B) (op : A → A → B) : Term → B
  | .s => z
  | .app l r => op (f l) (f r)

theorem attrNode {A B : Type} [FinStates B] {f : Term → A}
    (hf : Attribute f) (z : B) (op : A → A → B) : Attribute (node f z op) := by
  exact attrRec hf z (fun l r _ _ => op l r) rfl (fun _ _ => rfl)

theorem attrEq (u : Term) : Attribute (fun t => t == u) := by
  induction u with
  | s => apply attrRec attrConst true (fun _ _ _ _ => false) rfl; intro l r; rfl
  | app l r hl hr =>
    apply attrRec (attrPair hl hr) false (fun x y _ _ => x.1 && y.2) rfl
    intro x y
    apply Bool.eq_iff_iff.mpr
    simp

private def leftIsS := node (fun t => t == s) false (fun left _ => left)
private def leftIs1 := node leftIsS false (fun left _ => left)

private theorem eq_root_none (l r : Term) : (root l r).isNone = !leftIs1 l := by
  cases l with
  | s => rfl
  | app f a => cases f with
    | s => rfl
    | app h b => cases h <;> rfl

private theorem attrNF : Attribute nf := by
  have h := attrNode (attrNode (attrEq s) false (fun left _ => left)) false (fun left _ => left)
  apply attrRec h true (fun ll _ nl nr => !ll && nl && nr) rfl
  intro l r; simp only [nf,eq_root_none]; rfl

private theorem attrWord (g) : Attribute (isWord g) := by
  have hs := attrPair (attrEq s) (attrPair (attrEq A) (attrPair (attrEq B) (attrEq g)))
  apply attrRec hs false (fun l r _ wr => if l.1 then r.2.2.2 else (l.2.1 || l.2.2.1) && wr) rfl
  intro l r; by_cases h : l = s <;> simp [isWord,h]

private theorem attrUnary (g) : Attribute (isUnaryWord g) := by
  apply attrRec (attrPair (attrEq s) (attrWord g)) false (fun l r _ _ => l.1 && r.2) rfl
  intro l r; cases l <;> rfl

private theorem attrV (g) : Attribute (isV g) := by
  apply attrRec (attrUnary g) false (fun l r _ _ => l && r) rfl
  intro l r; rfl

private def headWord (g) := node (fun t => (t == A || t == B,isWord g t)) false
  (fun l r => l.1 && r.2)
private def headFrame (g) := node (fun t => (t == s || t == A,isV g t)) false
  (fun l r => l.1 && r.2)

/-- Any fixed finite-valued classification of the returned word, including a
    calibration bit, compiles to a finite scanner on arbitrary ground trees. -/
theorem scanAttribute {X : Type} [FinStates X] (g) (classify : Term → X) (hc : Attribute classify) :
    Attribute (fun t => (read g t).map classify) := by
  have bits (a b : Term) := attrMap (attrPair (attrEq a) (attrEq b)) (fun x => x.1 || x.2)
  have hh : Attribute (headWord g) := attrNode (attrPair (bits A B) (attrWord g)) false _
  have hf : Attribute (headFrame g) := attrNode (attrPair (bits s A) (attrV g)) false _
  have all := attrPair (attrPair hh hf) (attrPair (attrV g) hc)
  apply attrRec all none (fun l r _ rr =>
    if l.1.1 && r.2.1 then some l.2.2 else if l.1.2 then rr else none) rfl
  intro l r
  cases l with
  | s => simp [read,headWord,headFrame,node]
  | app h a =>
    simp only [read,headWord,headFrame,node]
    split <;> simp_all
    split <;> simp_all

inductive Action (Q : Type) where
  | stop (accept : Bool)
  | fast (next : Q)
  | slow (next : Q)

def perform {Q} (a : Action Q) (fast slow : Q → Bool) : Bool :=
  match a with
  | .stop b => b
  | .fast q => fast q
  | .slow q => slow q

structure Control (Q X : Type) where
  onA : Q → Action Q
  onB : Q → Option X → Action Q

/-- A fixed controller at a raw slot can stop, follow the fast continuation, or
    follow the delayed continuation. The second result is the right child's
    first result, enabling a delayed transition without arbitrary search. -/
def evaluate {Q X} (g : Term) (classify : Term → X) (c : Control Q X) :
    Term → (Q → Bool) × (Q → Bool)
  | .s => (fun _ => false, fun _ => false)
  | .app l r =>
    let lres := evaluate g classify c l
    let rres := evaluate g classify c r
    let run := fun q =>
      match slot g (l ⋆ r) with
      | none => false
      | some (.a _) => perform (c.onA q) rres.1 rres.1
      | some (.b _ _ scan) => perform (c.onB q ((read g scan).map classify)) lres.1 rres.2
    (run, rres.1)

private def aField (g) := node (fun t => (isUnaryWord g t,isV g t)) false (fun l r => l.1 && r.2)
private def splitField {X : Type} (g) (classify : Term → X) :=
  node (fun t => (nf t,(read g t).map classify)) (none : Option (Option X))
    (fun l r => if r.1 then none else some l.2)

/-- Concrete finite bottom-up implementation of any finite controller on the
    two native routes. Its state holds the answer for every incoming control
    state, and the corresponding table for the node's right child. -/
theorem routeAttribute {Q X : Type} [FinStates Q] [DecidableEq Q] [FinStates X]
    (g) (classify : Term → X) (hc : Attribute classify) (c : Control Q X) :
    Attribute (evaluate g classify c) := by
  have af : Attribute (aField g) := attrNode (attrPair (attrUnary g) (attrV g)) false _
  have sf : Attribute (splitField g classify) := attrNode (attrPair attrNF (scanAttribute g classify hc)) none _
  have all := attrPair attrNF (attrPair af sf)
  let no : Q → Bool := fun _ => false
  apply attrRec all (no,no) (fun l r L R =>
    (fun q => if r.1 then false else if l.1 then
        if l.2.1 then perform (c.onA q) R.1 R.1 else false
      else match r.2.2 with
        | none => false
        | some val => perform (c.onB q val) L.1 R.2, R.1)) rfl
  intro l r
  apply Prod.ext
  · funext q
    cases hr : nf r with
    | true => simp [evaluate,slot,hr]
    | false =>
      cases hl : nf l with
      | true =>
        cases l with
        | s => simp [evaluate,slot,hr,hl,aField,node]
        | app a b =>
          cases hm : (isUnaryWord g a && isV g b) <;> simp [evaluate,slot,hr,hl,aField,node,hm]
      | false =>
        cases r with
        | s => simp [nf] at hr
        | app x y =>
          cases hs : nf y <;> simp [evaluate,slot,hl,hr,hs,splitField,node]
  · rfl

#print axioms scanAttribute
#print axioms routeAttribute
end TwoScans.Observer
