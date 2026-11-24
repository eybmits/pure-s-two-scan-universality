import ShellAutomata
import Scan

namespace TwoScans.Automata
open Term Frames

/-- Evaluate a right-to-left word fold only on authentic wrapper spines.
    This structural parser is also the specification of the finite-state version. -/
def wordValue {Q : Type} (g : Term) (start : Q) (step : Bool → Q → Q) : Term → Option Q
  | s => none
  | .app f r =>
    if f = s then (if r = g then some start else none)
    else if f = A then (wordValue g start step r).map (step false)
    else if f = B then (wordValue g start step r).map (step true)
    else none

theorem wordValue_word {Q} (g : Term) (start : Q) (step : Bool → Q → Q) (w) :
    wordValue g start step (word g w) = some (w.foldr step start) := by
  induction w with
  | nil => simp [word,wordValue]
  | cons x w ih =>
    cases x <;> simp [word,wordValue,ih,A,B]

theorem wordValue_some {Q} (g : Term) (start : Q) (step : Bool → Q → Q) (t : Term) (q : Q) :
    wordValue g start step t = some q ↔ ∃ w, t = word g w ∧ q = w.foldr step start := by
  constructor
  · induction t generalizing q with
    | s => intro e; cases e
    | app f r _ ihr =>
      intro h
      simp only [wordValue] at h
      split at h
      · split at h
        · rename_i hf hr; subst f; subst r; cases h; exact ⟨[],rfl,rfl⟩
        · cases h
      · split at h
        · rename_i isA; subst f
          cases e : wordValue g start step r with
          | none => simp [e] at h
          | some q' =>
            obtain ⟨w,rfl,rfl⟩ := ihr _ e
            simp only [e,Option.map_some,Option.some.injEq] at h
            exact ⟨false::w,rfl,h.symm⟩
        · split at h
          · rename_i isB; subst f
            cases e : wordValue g start step r with
            | none => simp [e] at h
            | some q' =>
              obtain ⟨w,rfl,rfl⟩ := ihr _ e
              simp only [e,Option.map_some,Option.some.injEq] at h
              exact ⟨true::w,rfl,h.symm⟩
          · cases h
  · rintro ⟨w,rfl,rfl⟩; exact wordValue_word .. 

/-- Lift the finite deterministic word algebra to the corresponding ground
    pure-S wrapper language. Only the finite product of the four pattern states
    and one optional word-state is carried up the tree. -/
theorem regular_word {Q : Type} [FinStates Q] (g : Term)
    (start : Q) (step : Bool → Q → Q) (accept : Q → Bool) :
    Regular (fun t => ∃ w, t = word g w ∧ accept (w.foldr step start) = true) := by
  obtain ⟨K,ik,k,pk,hk⟩ := regular_exact g
  obtain ⟨X,ix,x,px,hx⟩ := regular_exact s
  obtain ⟨Y,iy,y,py,hy⟩ := regular_exact A
  obtain ⟨Z,iz,z,pz,hz⟩ := regular_exact B
  haveI := ik
  haveI := ix
  haveI := iy
  haveI := iz
  let base := (k.zip x).zip (y.zip z)
  let f := base.extend (none : Option Q) (fun l r =>
    if px l.1.1.2 then (if pk r.1.1.1 then some start else none)
    else if py l.1.2.1 then r.2.map (step false)
    else if pz l.1.2.2 then r.2.map (step true) else none)
  have eval (t : Term) : (f.run t).2 = wordValue g start step t := by
    induction t with
    | s => rfl
    | app l r _ ir =>
      change (if px (f.run l).1.1.2 then (if pk (f.run r).1.1.1 then some start else none)
              else if py (f.run l).1.2.1 then ((f.run r).2).map (step false)
              else if pz (f.run l).1.2.2 then ((f.run r).2).map (step true) else none) = _
      rw [show (f.run l).1 = _ from Fold.extend_base ..,show (f.run r).1 = _ from Fold.extend_base ..]
      simp only [base,Fold.zip_run,ir,hk,hx,hy,hz,wordValue]
  refine ⟨_,inferInstance,f,(fun z => z.2.elim false accept),?_⟩
  intro t; dsimp only
  rw [eval]
  constructor
  · cases e : wordValue g start step t with
    | none => intro h; cases h
    | some q =>
      intro ok
      obtain ⟨w,rfl,rfl⟩ := (wordValue_some _ _ _ _ _).mp e
      exact ⟨w,rfl,ok⟩
  · rintro ⟨w,rfl,h⟩
    rw [wordValue_word]; exact h

theorem regular_wrapper (g : Term) : Regular (fun t => ∃ w, t = word g w) := by
  obtain ⟨Q,inst,a,p,h⟩ := regular_word g () (fun _ _ => ()) (fun _ => true)
  exact ⟨Q,inst,a,p,fun t => by rw [h]; simp⟩

theorem regular_operand (g : Term) : Regular (Scan.VClass g) := by
  have unary := regular_app regular_leaf (regular_wrapper g)
  obtain ⟨Q,inst,a,p,h⟩ := regular_app unary unary
  refine ⟨Q,inst,a,p,?_⟩
  intro t
  rw [h]
  constructor
  · rintro ⟨l,r,rfl,⟨_,_,rfl,rfl,w,rfl⟩,_,_,rfl,rfl,v,rfl⟩
    exact ⟨w,v,rfl⟩
  · rintro ⟨w,v,rfl⟩
    exact ⟨_,_,rfl,⟨_,_,rfl,rfl,w,rfl⟩,_,_,rfl,rfl,v,rfl⟩

#print axioms regular_word
#print axioms regular_operand
end TwoScans.Automata
