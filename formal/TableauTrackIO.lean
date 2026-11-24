import TableauTracks

namespace TwoScans.Tableau.OneTape
open TrackLayout
variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- A witness at the calibrated dual-track interface. The proposed V track
and unary displacement are arbitrary; soundness includes forged candidates.
Actual tags, wrapper bits and the fixed observer are treated in other layers. -/
def TrackOutput (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (bit : Γ → Option Bool)
    (start : Cfg Q Γ) (out : List Bool) : Prop :=
  ∃ (k : Nat) (before : List (List (Tile (Color Q Γ)))) (last : List (Color Q Γ))
    (vs : List (Option (Color Q Γ))) (w : Nat),
    0 < w ∧
    (before.map (List.map Tile.center) ++ [last]).head? = some (encode (pad blank start k)) ∧
    (∀ r ∈ before, tileCheck (rule δ) none r = true) ∧
    TrackTests (writeSites before last) vs w ∧
    haltSeen halt last = true ∧ output bit last = out

theorem dual_track_iff_machine_output
    (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (bit : Γ → Option Bool)
    (quiet : bit blank = none) (start : Cfg Q Γ) (out : List Bool) :
    TrackOutput δ blank halt bit start out ↔
    ∃ n, let c := run (advance δ blank) start n
         halt c.state = true ∧ output bit (encode c) = out := by
  rw [← tableau_iff_machine_output δ blank halt bit quiet start out]
  constructor
  · rintro ⟨k,b,l,v,w,hw,head,loc,probes,accept,value⟩
    exact ⟨k,b,l,w,tableau_tracks_sound _ _ _ _ hw head loc probes,accept,value⟩
  · rintro ⟨k,b,l,w,pass,accept,value⟩
    obtain ⟨hw,head,loc,probes⟩ := tableau_tracks_complete _ _ _ _ pass
    exact ⟨k,b,l,_,w,hw,head,loc,probes,accept,value⟩

/-- A halted computation leaves its tape, state and position fixed. -/
def stopped (δ : Table Q Γ) (halt : Q → Bool) : Table Q Γ :=
  fun q a => if halt q then ⟨q,a,.stay⟩ else δ q a

private theorem run_add {C} (f : C → C) (x : C) (n k : Nat) :
    run f x (n+k) = run f (run f x n) k := by
  induction n generalizing x with
  | zero => simp [run]
  | succ n ih => simpa [Nat.succ_add,run] using ih (f x)

omit [DecidableEq Q] [DecidableEq Γ] in
private theorem still (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (c : Cfg Q Γ)
    (h : halt c.state = true) (n : Nat) : run (advance (stopped δ halt) blank) c n = c := by
  have stays : advance (stopped δ halt) blank c = c := by simp [advance,stopped,h]
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, stays] using ih

/-- Even certificates with different proposed widths and different claimed
halt times return exactly the same bit string. -/
theorem unique_track_output
    (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (bit : Γ → Option Bool)
    (quiet : bit blank = none) (start : Cfg Q Γ) {x y : List Bool}
    (hx : TrackOutput (stopped δ halt) blank halt bit start x)
    (hy : TrackOutput (stopped δ halt) blank halt bit start y) : x = y := by
  obtain ⟨m, hm, ex⟩ := (dual_track_iff_machine_output _ _ _ _ quiet start x).mp hx
  obtain ⟨n, hn, ey⟩ := (dual_track_iff_machine_output _ _ _ _ quiet start y).mp hy
  have coincide {m n : Nat} (hmn : m ≤ n)
      (hh : halt (run (advance (stopped δ halt) blank) start m).state = true) :
      run (advance (stopped δ halt) blank) start n =
      run (advance (stopped δ halt) blank) start m := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [run_add, still δ blank halt _ hh]
  by_cases h : m ≤ n
  · rw [coincide h hm] at ey
    exact ex.symm.trans ey
  · rw [coincide (by omega : n ≤ m) hn] at ex
    exact ex.symm.trans ey

#print axioms dual_track_iff_machine_output
#print axioms unique_track_output
end TwoScans.Tableau.OneTape
