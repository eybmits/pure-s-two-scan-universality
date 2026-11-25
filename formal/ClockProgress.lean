import Serial

namespace TwoScans.ClockProgress
open Term SerialTableau

/-- Count the old innermost sites which have changed at their original addresses.
The argument `new` is unrestricted; correctness only uses serializations of a round. -/
def progress : Term → Term → Nat
  | .s, _ => 0
  | .app l r, t =>
    match innermostRoot (.app l r) with
    | some _ => if .app l r = t then 0 else 1
    | none => match t with
      | .s => 0
      | .app a b => progress l a + progress r b

private theorem root_moves {f a u : Term} (h : innermostRoot (.app f a) = some u) :
    .app f a ≠ u := by
  cases f with
  | s => simp [innermostRoot,rootRule] at h
  | app g y => cases g with
    | s => simp [innermostRoot,rootRule] at h
    | app k x => cases k with
      | app m n => simp [innermostRoot,rootRule] at h
      | s =>
        simp only [innermostRoot,rootRule] at h
        split at h <;> simp_all only [Option.some.injEq,reduceCtorEq]
        subst u
        intro eq
        injection eq with eq _
        injection eq with eq _
        have hs := congrArg size eq
        simp [size] at hs

@[simp] theorem progress_self (t : Term) : progress t t = 0 := by
  induction t with
  | s => rfl
  | app l r hl hr =>
    cases e : innermostRoot (.app l r) <;> simp [progress,e,hl,hr]

@[simp] theorem progress_parallel (t : Term) : progress t (parallel t) = (sweep t).length := by
  induction t with
  | s => rfl
  | app l r hl hr =>
    cases e : innermostRoot (.app l r) with
    | none => simp [progress,parallel,sweep,e,hl,hr]
    | some u => simp [progress,parallel,sweep,e,root_moves e]

/-- The readout advances by one at each individual contraction of the sweep. -/
theorem progress_sweep (t : Term) (k : Nat) (hk : k < (sweep t).length) :
    progress t ((sweep t)[k]) = k + 1 := by
  induction t generalizing k with
  | s => simp [sweep] at hk
  | app l r hl hr =>
    cases e : innermostRoot (.app l r) with
    | some u =>
      have hk' : k < 1 := by simpa [sweep,e] using hk
      have z : k=0 := by omega
      subst k
      simp [sweep,e,progress,root_moves e]
    | none =>
      have hk' : k < (sweep l).length + (sweep r).length := by simpa [sweep,e] using hk
      by_cases left : k < (sweep l).length
      · simp [sweep,e,List.getElem_append_left, left, progress,hl k left]
      · have rr : k - (sweep l).length < (sweep r).length := by omega
        have past : ((sweep l).map (fun t => app t r)).length ≤ k := by simp; omega
        simp [sweep,e,List.getElem_append_right past,progress,hr _ rr]
        omega

end TwoScans.ClockProgress
#print axioms TwoScans.ClockProgress.progress_sweep
