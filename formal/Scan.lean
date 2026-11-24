import FramesBridge
import Tags

namespace TwoScans.Scan
open Term Frames

def frame : Bool → Term → Term
  | false, v => s ⋆ v
  | true, v => A ⋆ v

def stack (v : Term) : List Bool → Term → Term
  | [], t => t
  | b::bs, t => frame b v ⋆ stack v bs t

/-- The actual scan for every word prefix, including the exhausted prefix. -/
theorem peel {g v} (hg : nf g = true) (hv : nf v = true) (pre rest : List Bool) :
    Strict pre.length (word g (pre ++ rest) ⋆ v) (stack v pre (word g rest ⋆ v)) := by
  induction pre with
  | nil => exact .zero _
  | cons b pre ih =>
    have hw := word_normal hg (pre ++ rest)
    have hf : nf (frame b v) = true := by cases b <;> simp [frame,A,nf,root,hv]
    have lift := ih.under hf
    cases b <;> apply Strict.next
    all_goals first | simp [word, nf, root, A, B] | skip
    all_goals simpa [List.cons_append,word, A, B, pi, nf, root, hw, hv, frame, stack] using lift

theorem normalGuard {t} (k : Nat) (normal : Normal t) : Guard k t := by
  induction t with
  | s => exact .leaf
  | app a b ha hb =>
    exact .node (ha (normal.sub (.left .here))) (hb (normal.sub (.right .here)))
      (fun z st => (normal z st).elim)

theorem guardedEnd {g v} (hg : nf g = true) (hv : nf v = true) (w : List Bool) :
    Guard (size v) (stack v w ((s ⋆ g) ⋆ v)) ∧
    size v < size (stack v w ((s ⋆ g) ⋆ v)) := by
  induction w with
  | nil =>
    constructor
    · apply normalGuard
      apply (nf_iff_normal _).1
      simp [stack,nf,root,hg,hv]
    · simp [stack,size]; omega
  | cons b w ih =>
    have hn : nf (frame b v) = true := by cases b <;> simp [frame,nf,root,A,hv]
    constructor
    · exact .node (normalGuard _ ((nf_iff_normal _).1 hn)) ih.1 (fun _ _ => ih.2)
    · simp only [stack,size]
      have := ih.2
      omega

def operand (x y : Term) := (s ⋆ x) ⋆ (s ⋆ y)
def VClass (g t : Term) := ∃ u w : List Bool, t = operand (word g u) (word g w)

theorem wordSize (g) (w : List Bool) : size g < size (word g w) := by
  induction w with
  | nil => simp [word,size]
  | cons b w ih => cases b <;> simp [word,A,B,size] <;> omega

theorem noOperandInWord {g x} (big : 3 ≤ size g) (ox : VClass g x) (w : List Bool) :
    ¬ Occ x (word g w) := by
  obtain ⟨a,b,rfl⟩ := ox
  have ha := wordSize g a
  have hb := wordSize g b
  let v := operand (word g a) (word g b)
  have hsize : size g < size v := by simp only [v,operand,size]; omega
  have nsmall (t : Term) (ht : size t ≤ size g) : ¬Occ v t := by
    intro o
    have := o.sizeLE
    omega
  change ¬Occ v _
  induction w with
  | nil =>
    intro o
    rcases o.appCases with eq | inS | ing
    · simp [v,operand] at eq
    · exact nsmall s (by simp [size]; omega) inS
    · exact nsmall g (by omega) ing
  | cons c w ih =>
    intro o
    cases c with
    | false =>
      rcases o.appCases with eq | left | right
      · have eq' : word g a = s := (Term.app.inj (Term.app.inj eq).1).2
        rw [eq'] at ha
        simp [size] at ha
        omega
      · exact nsmall A (by simp [A,size]; omega) left
      · exact ih right
    | true =>
      rcases o.appCases with eq | left | right
      · have eq' : word g a = A := (Term.app.inj (Term.app.inj eq).1).2
        rw [eq'] at ha
        simp [A,size] at ha
        omega
      · exact nsmall B (by simp [B,A,size]; omega) left
      · exact ih right

theorem noOperandUnary {g x} (big : 3 ≤ size g) (ox : VClass g x) (w : List Bool) :
    ¬ Occ x (s ⋆ word g w) := by
  intro o
  rcases o.appCases with eq | insideS | insideWord
  · obtain ⟨a,b,h⟩ := ox
    rw [h] at eq
    simp [operand] at eq
  · obtain ⟨a,b,h⟩ := ox
    rw [h] at insideS
    cases insideS
  · exact noOperandInWord big ox w insideWord

/-- The operand test compares a regular shape only. In any reduct of a real
    scanner, every subtree of that shape is its precise original operand. -/
theorem operandIdentity {g t x} (hg : nf g = true) (big : 3 ≤ size g) (w : List Bool)
    (steps : Steps (word g w ⋆ operand (word g w) (word g w)) t)
    (o : Occ x t) (ox : VClass g x) : x = operand (word g w) (word g w) := by
  let p := word g w
  let v := operand p p
  have hw := word_normal hg w
  have hv : nf v = true := by simp [v,p,operand,nf,root,hw]
  have classV : VClass g v := ⟨w,w,rfl⟩
  obtain ⟨a,b,rfl⟩ := ox
  have classX : VClass g (operand (word g a) (word g b)) := ⟨a,b,rfl⟩
  have cut := intactAnchor ((nf_iff_normal _).1 hw) ((nf_iff_normal _).1 hv) steps o
  rcases cut with origP | origV | fresh
  · exact (noOperandInWord big classX w origP).elim
  · rcases origV.appCases with top | inL | inR
    · exact top
    · exact (noOperandUnary big classX w inL).elim
    · exact (noOperandUnary big classX w inR).elim
  · exact (noOperandUnary big classV b fresh).elim

/-- All later ages are safe, even though the putative operand was tested
    by a regular shape and the computation can have arbitrarily large frames. -/
theorem noFalseScanAfterEnd {g f z u} (hg : nf g = true) (big : 3 ≤ size g)
    (w : List Bool) (later : Nat) (oz : VClass g z)
    (o : Occ (f ⋆ z) (rounds later (rounds w.length
      (word g w ⋆ operand (word g w) (word g w))))) : ¬Step (f ⋆ z) u := by
  let p := word g w
  let v := operand p p
  have hw := word_normal hg w
  have hv : nf v = true := by simp [v,p,operand,nf,root,hw]
  have run := stepsAppend (roundsSteps (p ⋆ v) w.length) (roundsSteps _ later)
  have eqv := operandIdentity hg big w run ((Occ.right .here).trans o) oz
  have endEq : rounds w.length (p ⋆ v) = stack v w ((s ⋆ g) ⋆ v) := by
    simpa [p,word] using (peel hg hv w []).result
  rw [endEq] at o
  apply noLateShortCall (guardedEnd hg hv w).1 (roundsSteps _ later) o
  rw [eqv]
  exact Nat.le_refl _

#print axioms peel
#print axioms operandIdentity
#print axioms noFalseScanAfterEnd
end TwoScans.Scan
