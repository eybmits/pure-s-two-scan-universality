import Frames

/-! A deterministic single-contraction schedule. In each sweep, contract exactly
the old innermost redexes, from left to right. The Boolean gate may inspect the
two copies, but the schedule never inspects that gate or its decoder. -/
namespace SerialTableau
open TwoScans TwoScans.Term

def rootRule : Term → Option Term
  | .app (.app (.app .s x) y) z => some (.app (.app x z) (.app y z))
  | _ => none

def normalB : Term → Bool
  | .s => true
  | .app f a => (rootRule (.app f a)).isNone && normalB f && normalB a

def innermostRoot : Term → Option Term
  | .s => none
  | .app f a =>
    match rootRule (.app f a) with
    | none => none
    | some u => if normalB f && normalB a then some u else none

/-- One simultaneous round, including the fixed point on normal terms. -/
def parallel : Term → Term
  | .s => .s
  | .app f a =>
    (innermostRoot (.app f a)).getD (.app (parallel f) (parallel a))

theorem rootRule_agrees (f a : Term) : rootRule (.app f a) = Frames.root f a := by
  cases f with
  | s => rfl
  | app l y =>
    cases l with
    | s => rfl
    | app k x => cases k <;> rfl

theorem normalB_agrees (t : Term) : normalB t = Frames.nf t := by
  induction t with
  | s => rfl
  | app f a hf ha => simp only [normalB, Frames.nf, rootRule_agrees, hf, ha]

/-- Agreement with the independently defined maximal parallel round used
by the native reduction identities in Frames.lean. -/
theorem parallel_agrees (t : Term) : parallel t = Frames.pi t := by
  induction t with
  | s => rfl
  | app f a hf ha =>
    simp only [parallel, innermostRoot, rootRule_agrees, normalB_agrees, hf, ha, Frames.pi]
    cases ef : Frames.nf f <;> cases ea : Frames.nf a <;> cases er : Frames.root f a <;>
      simp_all [Frames.fixed]

theorem innermostRoot_sound {f a u : Term}
    (h : innermostRoot (.app f a) = some u) :
    Step (.app f a) u ∧ Normal f ∧ Normal a := by
  simp only [innermostRoot, rootRule_agrees, normalB_agrees] at h
  cases er : Frames.root f a with
  | none => simp [er] at h
  | some v =>
    cases ef : Frames.nf f <;> cases ea : Frames.nf a <;> simp [er, ef, ea] at h
    subst v
    exact ⟨Frames.root_sound er, (Frames.nf_iff_normal _).mp ef,
      (Frames.nf_iff_normal _).mp ea⟩

/-- The full term after each individual contraction in the current sweep. -/
def sweep : Term → List Term
  | .s => []
  | .app f a =>
    match innermostRoot (.app f a) with
    | some u => [u]
    | none => (sweep f).map (fun t => .app t a) ++
              (sweep a).map (fun t => .app (parallel f) t)

inductive One : Term → Term → Prop where
  | root {t u} : innermostRoot t = some u → One t u
  | left {a b} (r : Term) : One a b → One (.app a r) (.app b r)
  | right {a b} (l : Term) : One a b → One (.app l a) (.app l b)

inductive Path : Term → List Term → Term → Prop where
  | nil (x) : Path x [] x
  | cons {x y z xs} : One x y → Path y xs z → Path x (y :: xs) z

theorem Path.map {x z xs} (p : Path x xs z) {f : Term → Term}
    (respect : ∀ a b, One a b → One (f a) (f b)) :
    Path (f x) (xs.map f) (f z) := by
  induction p with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (respect _ _ h) ih

theorem Path.append {x y z xs ys} (p : Path x xs y) (q : Path y ys z) :
    Path x (xs ++ ys) z := by
  induction p with
  | nil => exact q
  | cons h _ ih => exact .cons h (ih q)

/-- A sweep is a path of single innermost contractions ending at precisely the
simultaneous successor. The recursive list fixes the left-to-right order. -/
theorem sweep_is_single_steps (x : Term) : Path x (sweep x) (parallel x) := by
  induction x with
  | s => exact .nil _
  | app f a hf ha =>
    cases h : innermostRoot (.app f a) with
    | some u =>
      simp only [sweep, parallel, h, Option.getD_some]
      exact .cons (.root h) (.nil _)
    | none =>
      simp only [sweep, parallel, h, Option.getD_none]
      exact (hf.map (fun _ _ s => .left a s)).append
        (ha.map (fun _ _ s => .right (parallel f) s))

def pack (a b : Term) := app (app s a) b

theorem parallel_pack (a b : Term) :
    parallel (pack a b) = pack (parallel a) (parallel b) := by
  simp [pack, parallel, innermostRoot, rootRule]

theorem sweep_pack (a b : Term) : sweep (pack a b) =
    (sweep a).map (fun t => pack t b) ++
    (sweep b).map (fun t => pack (parallel a) t) := by
  simp [pack, sweep, parallel, innermostRoot, rootRule, List.map_map, Function.comp_def]

def gate (hit : Term → Bool) : Term → Bool
  | .app (.app .s a) b => hit a && hit b
  | _ => false

/-- Include the starting boundary when asking for the first hit in a sweep.
Although either copy can pass a test between rounds, the left copy of this
first hit is always a passing parallel boundary. -/
theorem first_hit_in_sweep (hit : Term → Bool) (a z : Term)
    (seen : ((pack a a :: sweep (pack a a)).find? (gate hit)) = some z) :
    ∃ b c, z = pack b c ∧ hit b = true ∧ (b = a ∨ b = parallel a) := by
  by_cases h : hit a = true
  · simp [List.find?, gate, pack, h] at seen
    exact ⟨a, a, seen.symm, h, Or.inl rfl⟩
  · have hf : hit a = false := by cases e : hit a <;> simp_all
    have hn : ((sweep a).map (fun t => pack t a)).find? (gate hit) = none := by
      apply List.find?_eq_none.mpr
      intro t ht
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
      simp [gate, pack, hf]
    rw [sweep_pack] at seen
    have rest : ((sweep a).map (fun t => pack (parallel a) t)).find? (gate hit) =
        some z := by
      simpa only [List.find?_cons, show gate hit (pack a a) = false by simp [gate, pack, hf],
        Bool.false_eq_true, ↓reduceIte, List.find?_append, hn, Option.none_or] using seen
    obtain ⟨c, _, eq⟩ := List.mem_map.mp (List.mem_of_find?_eq_some rest)
    have hg : gate hit z = true := List.find?_some rest
    rw [← eq] at hg
    exact ⟨parallel a, c, eq.symm, (Bool.and_eq_true_iff.mp hg).1, Or.inr rfl⟩

end SerialTableau

#print axioms SerialTableau.sweep_is_single_steps
#print axioms SerialTableau.parallel_agrees
#print axioms SerialTableau.innermostRoot_sound
#print axioms SerialTableau.parallel_pack
#print axioms SerialTableau.sweep_pack
#print axioms SerialTableau.first_hit_in_sweep
