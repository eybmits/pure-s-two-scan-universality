import ObserverBlocks

namespace TwoScans.Observer
open Term Frames Automata TrackLayout WordBlocks

instance {R C : Type} [FinStates R] [FinStates C] : FinStates (Label R C) where
  enum := [.ub,.ue,.ve,.vb] ++ FinStates.enum.map .site ++ FinStates.enum.map .color
  covers x := by
    cases x <;> simp [FinStates.covers]

private def consShort (b : Bool) {n} (xs : Short n) : Short (n+1) :=
  ⟨b::xs.val,by simp; omega⟩

def clip (n : Nat) : Term → Short n :=
  match n with
  | 0 => fun _ => blank 0
  | n+1 => node (fun t => (t == A,t == B,clip n t)) (blank (n+1)) (fun l r =>
       if l.1 then consShort false r.2.2 else if l.2.1 then consShort true r.2.2 else blank _)

theorem clip_attr (n) : Attribute (clip n) := by
  induction n with
  | zero => exact ⟨Bool,inferInstance,⟨false,fun _ _ => false⟩,fun _ => blank _,fun _ => rfl⟩
  | succ n ih => exact attrNode (attrPair (attrEq A) (attrPair (attrEq B) ih)) _ _

theorem clip_word (n) (g : Term) (w) : (clip n (word g w)).val = w.take n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    cases w with
    | nil => rfl
    | cons b w =>
      cases b <;> simp [clip,word,node,A,B,consShort,ih]

def decodeBits {R : Type} [FinStates R] (A : Alphabet R) (bits : List Bool) : Option R :=
  FinStates.enum.find? (fun a => A.code a == bits)

theorem decodeBits_some {R : Type} [FinStates R] (A : Alphabet R) (bits : List Bool) (a : R) :
    decodeBits A bits = some a ↔ A.code a = bits := by
  constructor
  · intro h
    exact beq_iff_eq.mp (List.find?_some (p := fun c => A.code c == bits) h)
  · intro h
    cases e : decodeBits A bits with
    | none =>
      have hh := (List.find?_eq_none.mp e) a (FinStates.covers a)
      simp [h] at hh
    | some b =>
      have eq : A.code b = bits := beq_iff_eq.mp (List.find?_some (p := fun c => A.code c == bits) e)
      have := A.faithful b a (eq.trans h.symm)
      rw [this]

theorem decodeBits_code {R : Type} [FinStates R] (A : Alphabet R) (a : R) :
    decodeBits A (A.code a) = some a := (decodeBits_some ..).mpr rfl

def classifier {R : Type} [FinStates R] (g : Term) (A : Alphabet R)
    (boundary : R) (foot : List Bool) (t : Term) : Option R × Bool :=
  (decodeBits A (clip A.width t).val, decide (t = word g (A.code boundary ++ foot)))

theorem classifier_attribute {R : Type} [FinStates R] (g : Term) (A : Alphabet R) (boundary : R) (foot) :
    Attribute (classifier g A boundary foot) := by
  have h := attrPair (attrMap (clip_attr A.width) (fun xs => decodeBits A xs.val))
    (attrEq (word g (A.code boundary ++ foot)))
  obtain ⟨Q,inst,a,out,ok⟩ := h
  refine ⟨Q,inst,a,out,fun t => ?_⟩
  rw [ok]; simp [classifier]; apply Bool.eq_iff_iff.mpr; simp

private theorem word_inj {g : Term} {u v} (h : word g u = word g v) : u = v := by
  induction u generalizing v with
  | nil => cases v with
           | nil => rfl
           | cons b v => cases b <;> cases h
  | cons b u ih =>
    cases v with
    | nil => cases b <;> cases h
    | cons c v =>
      cases b <;> cases c <;> simp [word,A,B] at h
      all_goals exact congrArg _ (ih h)

theorem classifier_word {R : Type} [FinStates R] (g : Term) (A : Alphabet R) (boundary : R) (foot w) :
    classifier g A boundary foot (word g w) =
      (decodeBits A (w.take A.width), decide (w = A.code boundary ++ foot)) := by
  simp only [classifier,clip_word,Prod.mk.injEq,true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨word_inj,congrArg _⟩

#print axioms classifier_attribute
#print axioms classifier_word
end TwoScans.Observer
