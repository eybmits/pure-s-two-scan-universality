import Std

/- Pure word geometry after the two probes have been calibrated.
   'none' denotes the left wall, 'some c' any other color (including the
   right wall).  Thus a decoded row is exactly the cells after its left wall.
   The equality of streams tested below is the word-level meaning of all
   site comparisons, including the absence tests on the final row. -/
namespace TwoScans.Tableau
variable {C : Type}

def pack : List (List C) → List (Option C)
  | [] => []
  | r :: rs => none :: (r.map some ++ pack rs)

private def readCells : List (Option C) → List C
  | some c :: rest => c :: readCells rest
  | _ => []
private def skipCells : List (Option C) → List (Option C)
  | some _ :: rest => skipCells rest
  | rest => rest

private theorem read_pack (r : List C) (rs : List (List C)) :
    readCells (r.map some ++ pack rs) = r := by
  induction r with
  | nil => cases rs <;> rfl
  | cons c r ih => simp [readCells, ih]

private theorem skip_pack (r : List C) (rs : List (List C)) :
    skipCells (r.map some ++ pack rs) = pack rs := by
  induction r with
  | nil => cases rs <;> rfl
  | cons c r ih => simpa [skipCells] using ih

theorem pack_injective {a b : List (List C)} (h : pack a = pack b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [pack]
  | cons c cs ih =>
    cases b with
    | nil => simp [pack] at h
    | cons d ds =>
      have ht := (List.cons.inj h).2
      have he := congrArg readCells ht
      have hs := congrArg skipCells ht
      simp only [read_pack] at he
      simp only [skip_pack] at hs
      rw [he, ih hs]

private theorem drop_past_cells (cells : List C) (tail rest : List (Option C))
    (w : Nat) (h : (cells.map some ++ tail).drop w = none :: rest) :
    ∃ j, tail.drop j = none :: rest := by
  induction cells generalizing w with
  | nil => exact ⟨w, by simpa using h⟩
  | cons c cs ih =>
    cases w with
    | zero => simp at h
    | succ w => exact ih w (by simpa using h)

/-- A suffix beginning at a left wall is necessarily a suffix of whole rows. -/
theorem aligned_suffix (rows target : List (List C)) (w : Nat)
    (h : (pack rows).drop w = pack target) : target <:+ rows := by
  induction rows generalizing target w with
  | nil =>
    have hnil : pack ([] : List (List C)) = pack target := by simpa [pack] using h
    rw [← pack_injective hnil]
    exact ⟨[], rfl⟩
  | cons r rs ih =>
    cases target with
    | nil => simp
    | cons t ts =>
      cases w with
      | zero =>
        have he := pack_injective (by simpa using h)
        rw [he]
        exact ⟨[], rfl⟩
      | succ w =>
        obtain ⟨j, hj⟩ := drop_past_cells r (pack rs) (t.map some ++ pack ts) w (by
          simpa [pack] using h)
        exact (ih (t :: ts) j hj).trans (List.tail_suffix (r :: rs))

/-- The stream of expected successor colors has exactly one fewer left
wall. Matching it after a positive shift therefore identifies the entire
immediate successor row for every nonfinal row, without index assumptions. -/
theorem all_successors {first last : List C} {after before : List (List C)}
    {step : List C → List C} {w : Nat}
    (split : first :: after = before ++ [last]) (hw : 0 < w)
    (matchStream : (pack (first :: after)).drop w = pack (before.map step)) :
    after = before.map step := by
  have hlen := congrArg List.length split
  simp only [List.length_cons, List.length_append] at hlen
  cases before with
  | nil => simp at hlen; simpa using hlen
  | cons b bs =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0)
    obtain ⟨j, hj⟩ := drop_past_cells first (pack after)
      ((step b).map some ++ pack (bs.map step)) d (by simpa [pack] using matchStream)
    have hs := aligned_suffix after ((b :: bs).map step) j hj
    exact (hs.eq_of_length (by simp_all)).symm

def run (step : C → C) (x : C) : Nat → C
  | 0 => x
  | n+1 => run step (step x) n

def trace (step : C → C) (x : C) : Nat → List C
  | 0 => []
  | n+1 => x :: trace step (step x) n

theorem trace_length (step : C → C) (x : C) (n : Nat) : (trace step x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [trace, ih]

theorem trace_shift (step : C → C) (x : C) (n : Nat) :
    x :: (trace step x n).map step = trace step x n ++ [run step x n] := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [trace, run, ih]

theorem history_last {step : C → C} {x z : C} (before : List C)
    (h : x :: (before.map step) = before ++ [z]) : z = run step x before.length := by
  induction before generalizing x with
  | nil => exact (List.cons.inj h).1.symm
  | cons b bs ih =>
    obtain ⟨rfl, rest⟩ := List.cons.inj h
    exact ih rest

/-- Executable word-level reference. It receives the parsed row colors,
a proposed positive width, and an initial row. The full S observer implements
the stream equality via the two synchronized probes. -/
def check [DecidableEq C] (step : List C → List C) (initial : List C)
    (before : List (List C)) (last : List C) (w : Nat) : Bool :=
  let rows := before ++ [last]
  decide (w > 0 ∧ rows.head? = some initial ∧
    (pack rows).drop w = pack (before.map step))

theorem check_sound [DecidableEq C] (step : List C → List C) (initial : List C)
    (before : List (List C)) (last : List C) (w : Nat)
    (h : check step initial before last w = true) :
    last = run step initial before.length := by
  obtain ⟨hw, head, stream⟩ := of_decide_eq_true h
  generalize he : before ++ [last] = rows at head stream
  cases rows with
  | nil => simp at head
  | cons first after =>
    simp only [List.head?_cons, Option.some.injEq] at head
    subst first
    have hs := all_successors he.symm hw stream
    rw [hs] at he
    exact history_last before he.symm

theorem check_complete [DecidableEq C] (step : List C → List C) (initial : List C)
    (n : Nat) : check step initial (trace step initial n) (run step initial n)
        (initial.length + 1) = true := by
  have hs := trace_shift step initial n
  simp only [check, decide_eq_true_eq]
  rw [← hs]
  refine ⟨by omega, rfl, ?_⟩
  simp [pack]

#print axioms all_successors
#print axioms check_sound
#print axioms check_complete
end TwoScans.Tableau
