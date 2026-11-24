import TableauMachine

namespace TwoScans.Tableau.OneTape
variable {Q Γ : Type}
open Color

/-- Standard semi-infinite-tape step. Reading a previously unvisited cell at
the right yields blank. The finite list stores the visited part of the tape. -/
def advance (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) : Cfg Q Γ :=
  let z := δ c.state c.here
  match z.move with
  | .stay => ⟨c.left, z.state, z.write, c.right⟩
  | .left =>
    match c.left with
    | [] => ⟨[], z.state, z.write, c.right⟩
    | a :: as => ⟨as, z.state, a, z.write :: c.right⟩
  | .right =>
    match c.right with
    | [] => ⟨z.write :: c.left, z.state, blank, []⟩
    | a :: as => ⟨z.write :: c.left, z.state, a, as⟩

def pad (blank : Γ) (c : Cfg Q Γ) (k : Nat) : Cfg Q Γ :=
  {c with right := c.right ++ List.replicate k blank}

/-- A successful bounded step agrees with the unbounded source step up to
right blank padding. One step consumes at most one unit of reserve. -/
theorem pad_step (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) (k : Nat) :
    (∃ j, k ≤ j+1 ∧ bounded δ (pad blank c k) =
       some (pad blank (advance δ blank c) j)) ∨
    (k = 0 ∧ bounded δ (pad blank c k) = none) := by
  rcases c with ⟨l,q,a,r⟩
  generalize hz : δ q a = z
  rcases z with ⟨q',b,d⟩
  cases d <;> cases r <;> cases l <;> cases k
  all_goals first
    | (refine Or.inl ⟨_, Nat.le_succ _, ?_⟩; solve | simp [pad, bounded, advance, hz, List.replicate_succ])
    | (refine Or.inr ⟨rfl, ?_⟩; solve | simp [bounded, pad, hz])
    | (refine Or.inl ⟨_, Nat.le_refl _, ?_⟩; solve | simp [pad, bounded, advance, hz, List.replicate_succ])

private theorem dead_run (δ : Table Q Γ) (r : List Γ) (n : Nat) :
    run (sweep (rule δ) none) (dead r) n = dead r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, dead_fixed] using ih

/-- Every finite-width orbit at every time is either a blank-padded copy of
the genuine semi-infinite configuration or a permanently headless escape.
Padding with at least n cells makes escape impossible in n steps. -/
theorem finite_tracks_infinite (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) (n k : Nat) :
    (∃ j, run (sweep (rule δ) none) (encode (pad blank c k)) n =
       encode (pad blank (run (advance δ blank) c n) j)) ∨
    (k < n ∧ ∃ cells, run (sweep (rule δ) none) (encode (pad blank c k)) n = dead cells) := by
  induction n generalizing c k with
  | zero => exact Or.inl ⟨k,rfl⟩
  | succ n ih =>
    rcases pad_step δ blank c k with ⟨j, bound, move⟩ | ⟨zero, failed⟩
    · have actual := sweep_of_step δ _ _ move
      simp only [run, actual]
      rcases ih (advance δ blank c) j with h | ⟨h, cells, eq⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, cells, eq⟩
    · obtain ⟨cells, eq⟩ := sweep_of_escape δ _ failed
      exact Or.inr ⟨by omega, cells, by simp [run, eq, dead_run]⟩

def haltSeen (halt : Q → Bool) (r : List (Color Q Γ)) : Bool := r.any fun
  | .head q _ => halt q
  | _ => false

def output (bit : Γ → Option Bool) (r : List (Color Q Γ)) : List Bool := r.filterMap fun
  | .head _ a | .plain a => bit a
  | .wall => none

private theorem any_false (l : List Γ) : (l.any fun _ => false) = false := by
  induction l <;> simp_all

@[simp] theorem halt_encode (halt : Q → Bool) (c : Cfg Q Γ) :
    haltSeen halt (encode c) = halt c.state := by
  simp [haltSeen, encode, List.any_map, Function.comp_def, any_false]

@[simp] theorem halt_dead (halt : Q → Bool) (a : List Γ) :
    haltSeen (Γ := Γ) halt (dead a) = false := by
  simp [haltSeen, dead, List.any_map, Function.comp_def]

theorem output_pad (bit : Γ → Option Bool) (blank : Γ) (quiet : bit blank = none)
    (c : Cfg Q Γ) (k : Nat) :
    output bit (encode (pad blank c k)) = output bit (encode c) := by
  cases hb : bit c.here <;> simp [output, encode, pad, List.filterMap_append, List.filterMap_map, Function.comp_def,
    quiet, hb]

/-- At the site-comparison interface, a Boolean accepting certificate for a
bit string exists exactly when the standard one-tape machine reaches a
halting state that reads that bit string. State and alphabet can be Fin
types; the theorem is uniform in the deterministic instruction table. -/
theorem tableau_iff_machine_output [DecidableEq Q] [DecidableEq Γ]
    (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (bit : Γ → Option Bool)
    (quiet : bit blank = none) (start : Cfg Q Γ) (out : List Bool) :
    (∃ k before last w,
      siteCheck (rule δ) (encode (pad blank start k)) before last w = true ∧
      haltSeen halt last = true ∧ output bit last = out) ↔
    ∃ n, let c := run (advance δ blank) start n
         halt c.state = true ∧ output bit (encode c) = out := by
  constructor
  · rintro ⟨k, before, last, w, pass, done, outEq⟩
    have correct := siteCheck_sound _ _ _ _ _ pass
    rcases finite_tracks_infinite δ blank start before.length k with ⟨j,h⟩ | ⟨_,cells,h⟩
    · rw [correct, h, halt_encode] at done
      rw [correct, h, output_pad bit blank quiet] at outEq
      exact ⟨before.length, done, outEq⟩
    · rw [correct, h, halt_dead] at done
      contradiction
  · rintro ⟨n, done, outEq⟩
    let first := encode (pad blank start n)
    let st := sweep (rule δ) none
    have eq := finite_tracks_infinite δ blank start n n
    rcases eq with ⟨j,h⟩ | ⟨h,_⟩
    · refine ⟨n, (trace st first n).map (tiles (rule δ) none), run st first n,
        first.length+1, siteCheck_complete _ _ _, ?_, ?_⟩
      · change haltSeen halt (run (sweep (rule δ) none) (encode (pad blank start n)) n) = true
        rw [h,halt_encode]
        exact done
      · change output bit (run (sweep (rule δ) none) (encode (pad blank start n)) n) = out
        rw [h, output_pad bit blank quiet]
        exact outEq
    · omega

#print axioms finite_tracks_infinite
#print axioms tableau_iff_machine_output
end TwoScans.Tableau.OneTape
