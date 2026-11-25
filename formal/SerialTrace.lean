import ClockProgress
import SweepClock
import SerialReadout

namespace TwoScans.SerialTrace
open Frames SerialTableau SerialReadout

/-- Two clock copies, a normal encoding of the initial row, and the data tree. -/
def frame (left right literal data : Term) : Term := pack (pack left right) (pack literal data)
def clock := Shell.seed []
def start (literal data : Term) := frame clock clock literal data

/-- Only the current tree is read. A zero clock difference reports the stored initial row. -/
def read {Y : Type} (initial : Term → Option Y) (atRow : Nat → Term → Option Y) : Term → Option (Nat × Y)
  | .app (.app .s (.app (.app .s left) right)) (.app (.app .s literal) data) =>
    match ClockProgress.progress right left with
    | 0 => (initial literal).map fun y => (0,y)
    | k+1 => (atRow k data).map fun y => (k,y)
  | _ => none

/-- An observation at contraction index `j` belongs to a finite prefix of the fixed sweep path. -/
def At (seed : Term) (j : Nat) (t : Term) := ∃ b, (states seed b)[j]? = some t

private theorem runsFrame (a d : Term) (stable : parallel a = a) (n : Nat) :
    rounds n (start a d) = frame (rounds n clock) (rounds n clock) a (rounds n d) := by
  have ar : ∀ j, rounds j a = a := by
    intro j; induction j with
    | zero => rfl
    | succ i ih => rw [rounds_add i 1,ih]; exact (parallel_agrees _).symm.trans stable
  simp [start,frame,rounds_pack,ar]

private theorem sweep_frame (l a d : Term) (empty : sweep a = []) (stable : parallel a = a) :
    sweep (frame l l a d) =
      (sweep l).map (fun x => frame x l a d) ++
      (sweep l).map (fun y => frame (parallel l) y a d) ++
      (sweep d).map (fun z => frame (parallel l) (parallel l) a z) := by
  simp [frame,sweep_pack,parallel_pack,List.map_map,Function.comp_def,empty,stable]

private theorem state_extend (e : Term) (n : Nat) :
    states e (n+1) = states e n ++ sweep (rounds n e) := by
  simp [states,post]

private theorem length_mono (e : Term) {m n : Nat} (h : m ≤ n) :
    (states e m).length ≤ (states e n).length := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => rw [state_extend,List.length_append]; omega

/-- Each time index denotes at most one term, even if its witnesses use different sweep bounds. -/
theorem at_functional {e t u : Term} {j : Nat} (h : At e j t) (g : At e j u) : t = u := by
  have extend {m n : Nat} (le : m ≤ n) : ∃ rest, states e n = states e m ++ rest := by
    induction le with
    | refl => exact ⟨[], by simp⟩
    | step _ ih => obtain ⟨r,hr⟩ := ih; rw [state_extend,hr,List.append_assoc]; exact ⟨_,rfl⟩
  have lift {t : Term} {m n} (hm : (states e m)[j]? = some t) (le : m ≤ n) :
      (states e n)[j]? = some t := by
    obtain ⟨r,hr⟩ := extend le
    have pos := (List.getElem?_eq_some_iff.mp hm).1
    rw [hr,List.getElem?_append_left pos,hm]
  obtain ⟨m,hm⟩ := h; obtain ⟨n,hn⟩ := g
  exact Option.some.inj ((lift hm (Nat.le_max_left m n)).symm.trans (lift hn (Nat.le_max_right m n)))

private theorem sweep_sound {Y : Type} (initial : Term → Option Y) (get : Nat → Term → Option Y)
    (V : Nat → Y → Prop) (l a d : Term) (empty : sweep a = []) (stable : parallel a = a)
    (base : ∀ y, initial a = some y → V 0 y) (good : ∀ k y, get k d = some y → V k y)
    {z : Term} (mem : z ∈ sweep (frame l l a d)) {i y} (hit : read initial get z = some (i,y)) : V i y := by
  have atData (x w : Term) (h : read initial get (frame x w a d) = some (i,y)) : V i y := by
    cases hprog : ClockProgress.progress w x with
    | zero =>
      have h' : ∃ v, initial a = some v ∧ (0,v) = (i,y) := by
        simpa [read,frame,pack,hprog,Option.map_eq_some_iff] using h
      obtain ⟨v,hv,eq⟩ := h'; cases eq; exact base _ hv
    | succ k =>
      have h' : ∃ v, get k d = some v ∧ (k,v) = (i,y) := by
        simpa [read,frame,pack,hprog,Option.map_eq_some_iff] using h
      obtain ⟨v,hv,eq⟩ := h'; cases eq; exact good _ _ hv
  rw [sweep_frame l a d empty stable] at mem
  simp only [List.mem_append,List.mem_map] at mem
  rcases mem with ((⟨v,_,rfl⟩ | ⟨v,_,rfl⟩) | ⟨v,_,rfl⟩)
  · exact atData _ _ hit
  · exact atData _ _ hit
  · have h : ∃ v, initial a = some v ∧ (0,v) = (i,y) := by
      simpa [read,frame,pack,Option.map_eq_some_iff] using hit
    obtain ⟨v,hv,eq⟩ := h; cases eq; exact base _ hv

/-- All values read at individual contraction times are valid for their reported source index. -/
theorem all_samples {Y : Type} (initial : Term → Option Y) (get : Nat → Term → Option Y)
    (V : Nat → Y → Prop) {a d : Term} (empty : sweep a = []) (stable : parallel a = a)
    (base : ∀ y, initial a = some y → V 0 y) (good : ∀ n k y, get k (rounds n d) = some y → V k y)
    {j t i y} (atT : At (start a d) j t) (hit : read initial get t = some (i,y)) : V i y := by
  obtain ⟨b,hb⟩ := atT
  have mem := List.mem_of_getElem? hb
  clear hb
  induction b with
  | zero =>
    have h : t = start a d := by simpa [states,post] using mem
    subst t
    have h' : ∃ v, initial a = some v ∧ (0,v) = (i,y) := by
      simpa [start,frame,pack,read,Option.map_eq_some_iff] using hit
    obtain ⟨v,hv,eq⟩ := h'; cases eq; exact base _ hv
  | succ n ih =>
    rw [state_extend,List.mem_append] at mem
    rcases mem with old | cur
    · exact ih old
    · rw [runsFrame _ _ stable] at cur
      exact sweep_sound initial get V _ _ _ empty stable base (good n) cur hit

private theorem first_clock {a d : Term} (empty : sweep a = []) (stable : parallel a = a)
    (b i : Nat) (h : i < (sweep (rounds b clock)).length) :
    let l := rounds b clock
    let m := (states (start a d) b).length+i
    (states (start a d) (b+1))[m]? = some (frame (sweep l)[i] l a (rounds b d)) ∧
    m < (states (start a d) (b+1)).length := by
  dsimp only
  have eq : (states (start a d) (b+1))[(states (start a d) b).length+i]? =
      some (frame (sweep (rounds b clock))[i] (rounds b clock) a (rounds b d)) := by
    rw [state_extend,List.getElem?_append_right (by omega),runsFrame _ _ stable,sweep_frame _ _ _ empty stable]
    simp only [Nat.add_sub_cancel_left,List.append_assoc]
    rw [List.getElem?_append_left (by simpa using h), List.getElem?_map, List.getElem?_eq_getElem h]; rfl
  exact ⟨eq,(List.getElem?_eq_some_iff.mp eq).1⟩

/-- A single clock, starting at the literal initial row. The row index is recovered from
    the current term by comparing the two clock copies. The evaluator never consults it. -/
theorem chronological {Y : Type} (initial : Term → Option Y) (get : Nat → Term → Option Y)
    {a d : Term} (empty : sweep a = []) (stable : parallel a = a) (first : Y) (base : initial a = some first)
    (cofinal : ∀ i T : Nat, ∃ b y, T < b ∧ get i (rounds b d) = some y) :
    ∃ time : Nat → Nat, time 0 = 0 ∧ (∀ n, time n < time (n+1)) ∧
      ∀ n, ∃ t y, At (start a d) (time n) t ∧ read initial get t = some (n,y) := by
  classical
  have chooseRound (i prior : Nat) : ∃ b, prior < b ∧ i < (sweep (rounds b clock)).length ∧
      ∃ y, get i (rounds b d) = some y := by
    obtain ⟨T,cap⟩ := SweepClock.widening (i+1) []
    obtain ⟨b,y,late,got⟩ := cofinal i (max prior T)
    exact ⟨b, by omega, by have wide := cap b (by omega); exact wide, y,got⟩
  let pick (i prior : Nat) := Classical.choose (chooseRound i prior)
  have spec (i prior : Nat) := Classical.choose_spec (chooseRound i prior)
  let r (i : Nat) : Nat := Nat.rec (motive := fun _ => Nat) (pick 0 0) (fun k previous => pick (k+1) previous) i
  have props (i : Nat) : i < (sweep (rounds (r i) clock)).length ∧
      ∃ y, get i (rounds (r i) d) = some y := by
    cases i with
    | zero => exact (spec 0 0).2
    | succ k => exact (spec (k+1) (r k)).2
  have rise (i : Nat) : r i < r (i+1) := (spec (i+1) (r i)).1
  let time : Nat → Nat := fun i => match i with
    | 0 => 0
    | k+1 => (states (start a d) (r (k+1))).length+(k+1)
  refine ⟨time,rfl,?_,?_⟩
  · intro k
    cases k with
    | zero => dsimp [time]; omega
    | succ k =>
      have before := (first_clock (d:=d) empty stable (r (k+1)) (k+1) (props _).1).2
      have bt : (states (start a d) (r (k+1)+1)).length ≤ (states (start a d) (r (k+2))).length :=
        length_mono _ (rise (k+1))
      change (states (start a d) (r (k+1))).length+(k+1) < (states (start a d) (r (k+2))).length+(k+2)
      omega
  · intro i
    cases i with
    | zero => exact ⟨start a d,first,⟨0,by rfl⟩,by simp [start,frame,pack,read,base]⟩
    | succ k =>
      let l := rounds (r (k+1)) clock
      have cap := (props (k+1)).1
      obtain ⟨y,hy⟩ := (props (k+1)).2
      refine ⟨frame (sweep l)[k+1] l a (rounds (r (k+1)) d),y,
        ⟨r (k+1)+1,(first_clock (d:=d) empty stable (r (k+1)) (k+1) cap).1⟩,?_⟩
      simp [read,frame,pack,ClockProgress.progress_sweep,l,hy]

end TwoScans.SerialTrace
