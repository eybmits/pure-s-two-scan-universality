import ShellAnyTape

set_option linter.unusedSectionVars false
namespace TwoScans.TraceReadout
open Tableau OneTape AnyTape Automata Shell Frames WordBlocks TrackLayout PayloadBits

private theorem history_rows {C : Type} {step : C → C} {x z : C} (before : List C)
    (h : x :: before.map step = before ++ [z]) :
    before = trace step x before.length := by
  induction before generalizing x with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨rfl,rest⟩ := List.cons.inj h
    exact congrArg (List.cons x) (ih rest)

/-- The center records of every passing tableau are exactly the successive rows, in order. -/
theorem ordered_rows {C : Type} [DecidableEq C] (δ : Rule C) (initial : List C)
    (before : List (List (Tile C))) (last : List C) (w : Nat)
    (pass : siteCheck δ initial before last w = true) :
    before.map (List.map Tile.center) = trace (sweep δ none) initial before.length ∧
    last = run (sweep δ none) initial before.length := by
  refine ⟨?_,siteCheck_sound _ _ _ _ _ pass⟩
  obtain ⟨⟨⟨hw,head⟩,tilesOK⟩,sitesOK⟩ := by
    simpa only [siteCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using pass
  have shifted := (sites_iff _ _ _ (by simp)).mp sitesOK
  have nextRows : before.map (List.map Tile.next) =
      (before.map (List.map Tile.center)).map (sweep δ none) := by
    rw [List.map_map]
    exact List.map_congr_left (fun r hr => tile_sound _ _ r (tilesOK _ hr))
  rw [nextRows] at shifted
  generalize eq : before.map (List.map Tile.center) ++ [last] = rows at head shifted
  cases rows with
  | nil => cases head
  | cons first after =>
    have firstEq := Option.some.inj head
    subst first
    have successive := all_successors eq.symm hw shifted
    rw [successive] at eq
    simpa using history_rows _ eq.symm


variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [FinStates Q] [FinStates Γ]

private theorem staticRows (δ : Table Q Γ) (blank : Γ) (halt) (u) :
    siteTest δ blank halt u = true ↔ ∃ b last k input, u = writeSites b last ∧
      (∀ r ∈ b, tileCheck (liftRule δ blank) none r = true) ∧
      last.any (haltColor halt ∘ erase blank) = true ∧
      (b.map (List.map Tile.center) ++ [last]).head? = some (initialRow input k) := by
  unfold siteTest; rw [Static.rows_iff]
  have head (b : List (List (Tile (Mark (Color Q Γ))))) (last : List (Mark (Color Q Γ))) :
      (b.map (List.map Tile.center) ++ [last]).head? = some ((b.head?.map (List.map Tile.center)).getD last) := by
    cases b <;> rfl
  simp only [List.all_eq_true,input_iff,head,Option.some.injEq]
  constructor
  · rintro ⟨b,last,hu,hl,hf,x,k,hx⟩; exact ⟨b,last,k,x,hu,hl,hf,hx⟩
  · rintro ⟨b,last,k,x,hu,hl,hf,hx⟩; exact ⟨b,last,hu,hl,hf,x,k,hx⟩

private theorem forget_sweep (F : Rule C) (blank wall : C) (p : Option (Mark C)) (r : List (Mark C)) :
    (sweep (markedRule F blank wall) p r).map (forget blank wall) =
    sweep F (p.map (forget blank wall)) (r.map (forget blank wall)) := by
  induction r generalizing p with
  | nil => rfl
  | cons c cs ih => simp [sweep,markedRule,forget,List.head?_map,ih]

private theorem forget_run (δ : Table Q Γ) (blank : Γ) (r : List (Mark (Color Q Γ))) (n : Nat) :
    (run (sweep (liftRule δ blank) none) r n).map (erase blank) =
    run (sweep (rule δ) none) (r.map (erase blank)) n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp only [run,ih,forget_sweep,Option.map_none]

private theorem forget_initial (blank : Γ) (c : Cfg Q Γ) (k : Nat) :
    (initialRow (core c) k).map (erase blank) = encode (pad blank c (k+1)) := by
  simp [initialRow,core,encode,pad,erase,forget,List.map_map,Function.comp_def,List.append_assoc,List.replicate_succ]

private theorem final_halt (halt : Q → Bool) (blank : Γ) (r : List (Mark (Color Q Γ))) :
    r.any (haltColor halt ∘ erase blank) = haltSeen halt (r.map (erase blank)) := by
  rw [haltSeen,List.any_map]
  rfl

/-- Test the static and native scan gates on one tagged packet anywhere in a snapshot. -/
def Passing (δ : Table Q Γ) (blank : Γ) (accept : Q → Bool) (raw : List Bool) (t : Term) : Prop :=
  ∃ r, Occ (.app (tag raw) r) t ∧ wordTest δ blank accept raw = true ∧
      bodyTest (Q:=Q) (Γ:=Γ) r = true

private theorem trace_at {X} (f : X → X) (x : X) (n i : Nat) (hi : i ≤ n) :
    (trace f x n ++ [run f x n])[i]? = some (run f x i) := by
  induction n generalizing i x with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    rfl
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih (f x) i (by omega)

private theorem run_add {X} (f : X → X) (x : X) (n k : Nat) :
    run f x (n+k) = run f (run f x n) k := by
  induction n generalizing x with
  | zero => simp [run]
  | succ n ih => simpa [Nat.succ_add,run] using ih (f x)

private theorem survives {δ : Table Q Γ} {blank : Γ} {accept : Q → Bool}
    (c : Cfg Q Γ) (n k : Nat) (good :
     haltSeen accept (run (sweep (rule δ) none) (encode (pad blank c k)) n) = true)
    (i : Nat) (hi : i ≤ n) : ∃ padding,
      run (sweep (rule δ) none) (encode (pad blank c k)) i =
        encode (pad blank (run (advance δ blank) c i) padding) := by
  rcases finite_tracks_infinite δ blank c i k with live | ⟨_,cells,escaped⟩
  · exact live
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [run_add,escaped] at good
  have forever : run (sweep (rule δ) none) (dead cells) m = dead cells := by
    clear good
    induction m with | zero => rfl | succ m ih => simpa [run,dead_fixed] using ih
  rw [forever,halt_dead] at good; cases good

/-- In the word of *any* passing packet on this orbit, the i-th row is the i-th
    configuration of the actual source run, up to blank padding, for every i. -/
theorem packet_sound (δ : Table Q Γ) (blank : Γ) (accept : Q → Bool) (c : Cfg Q Γ)
    (raw : List Bool) (j : Nat) (found : Passing δ blank accept raw (rounds j (startTerm blank c))) :
    ∃ b last vs w, raw = payload (A Q Γ) (writeSites b last) vs w [] ∧
      ∀ i ≤ b.length, ∃ row padding,
        (b.map (List.map Tile.center) ++ [last])[i]? = some row ∧
        row.map (erase blank) = encode (pad blank (run (advance δ blank) c i) padding) := by
  obtain ⟨r,occ,wp,bp⟩ := found
  obtain ⟨pre,age,rfl,rfl⟩ := (shell_orbit_iff (key (A Q Γ) (core c)) raw r).mp ⟨j,occ⟩
  obtain ⟨us,vs,w,rawEq,hw,st⟩ := (Static.wordOK_iff _ [] _ _).mp wp
  rw [rawEq] at bp
  have probes := (Join.both_iff (A Q Γ) (FiniteCodes.wide _) FiniteCodes.starts FiniteCodes.ends
    [] us vs w hw).mp ⟨age,bp⟩
  obtain ⟨b,last,k,inp,rfl,tiles,done,head⟩ := (staticRows _ _ _ _).mp st
  obtain ⟨other,keyEq⟩ := genuine_key (A Q Γ) inp k _ _ _ _ head probes
  have same := key_unique (A Q Γ) (core c) inp pre other (rawEq.trans keyEq)
  subst inp
  have checked := tableau_tracks_sound (liftRule δ blank) _ b last hw head tiles probes
  obtain ⟨order,lastEq⟩ := ordered_rows _ _ _ _ _ checked
  rw [lastEq,final_halt,forget_run,forget_initial] at done
  refine ⟨b,last,vs,w,rawEq,?_⟩
  intro i hi
  obtain ⟨padding,pr⟩ := survives c b.length (k+1) done i hi
  refine ⟨run (sweep (liftRule δ blank) none) (initialRow (core c) k) i,padding,?_,?_⟩
  · rw [order,lastEq]; exact trace_at _ _ _ i hi
  · rw [forget_run,forget_initial,pr]

/-- One fixed finite-state projection of the packet word. `none` separates rows. -/
def readTrace (blank : Γ) (raw : List Bool) : List (Option (Color Q Γ)) :=
  (OutputStream.transduce (OutputStream.reader (A Q Γ) (some ∘ Site.current)) .header raw).map
    (Option.map (erase blank))

private theorem map_pack {X Y : Type} (f : X → Y) (rs : List (List X)) :
    (pack rs).map (Option.map f) = pack (rs.map (List.map f)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [pack,ih,List.map_map,Function.comp_def]

private theorem read_written (blank : Γ) b last vs w :
    readTrace (Q:=Q) blank (payload (A Q Γ) (writeSites b last) vs w []) =
      pack ((b.map (List.map Tile.center) ++ [last]).map (List.map (erase blank))) := by
  rw [readTrace,OutputStream.on_payload _ FiniteCodes.ends]
  simp only [List.filterMap_eq_map, current_write, map_pack]

def Correct (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) (rows : List (List (Color Q Γ))) :=
  ∀ i < rows.length, ∃ k, rows[i]? = some (encode (pad blank (run (advance δ blank) c i) k))

/-- Soundness for the executable reader on each accepted packet. -/
theorem read_sound (δ : Table Q Γ) (blank : Γ) (accept : Q → Bool) (c : Cfg Q Γ)
    (raw : List Bool) (j : Nat) (found : Passing δ blank accept raw (rounds j (startTerm blank c))) :
    ∃ rows, readTrace (Q:=Q) blank raw = pack rows ∧ rows ≠ [] ∧ Correct δ blank c rows := by
  obtain ⟨b,l,v,w,rfl,valid⟩ := packet_sound _ _ _ _ _ _ found
  refine ⟨_,read_written _ _ _ _ _,by simp,?_⟩
  intro i hi
  have bound : i ≤ b.length := by
    simpa only [List.length_map,List.length_append,List.length_singleton,Nat.lt_succ_iff] using hi
  obtain ⟨row,k,atRow,eq⟩ := valid i bound
  refine ⟨k,?_⟩
  rw [List.getElem?_map,atRow]; exact congrArg some eq

/-- Arbitrarily large padding may be chosen for the same source prefix. -/
theorem complete_with_padding (δ : Table Q Γ) (blank : Γ) (accept : Q → Bool)
    (c : Cfg Q Γ) (n k : Nat) (space : n ≤ k) (accepts : accept (run (advance δ blank) c n).state = true) :
    ∃ raw j rows, Passing δ blank accept raw (rounds j (startTerm blank c)) ∧
      readTrace (Q:=Q) blank raw = pack rows ∧ rows.length = n+1 ∧
      k < raw.length ∧ Correct δ blank c rows := by
  let initial := initialRow (core c) k
  let last := run (sweep (liftRule δ blank) none) initial n
  let before := (trace (sweep (liftRule δ blank) none) initial n).map (tiles (liftRule δ blank) none)
  let us := writeSites before last
  let vs := us.map Site.current
  let w := initial.length+1
  let raw := payload (A Q Γ) us vs w []
  have cert : siteCheck (liftRule δ blank) initial before last w = true := siteCheck_complete ..
  obtain ⟨hw,head,tiles,probes⟩ := tableau_tracks_complete _ _ _ _ cert
  obtain ⟨pre,keyEq⟩ := genuine_key (A Q Γ) (core c) k before last vs w head probes
  obtain ⟨age,gate⟩ := (Join.both_iff (A Q Γ) (FiniteCodes.wide _) FiniteCodes.starts FiniteCodes.ends
    [] us vs w hw).mpr probes
  have done : last.any (haltColor accept ∘ erase blank) = true := by
    dsimp [last,initial]; rw [final_halt,forget_run,forget_initial]
    rcases finite_tracks_infinite δ blank c n (k+1) with ⟨m,eq⟩ | ⟨lt,_⟩
    · rw [eq,halt_encode]; exact accepts
    · omega
  have st : siteTest δ blank accept us = true := (staticRows _ _ _ _).mpr
    ⟨before,last,k,core c,rfl,tiles,done,head⟩
  have yes := (Static.wordOK_iff (A Q Γ) [] (siteTest δ blank accept) raw).mpr
    ⟨us,vs,w,rfl,hw,st⟩
  obtain ⟨j,occ⟩ := shell_visible (key (A Q Γ) (core c)) pre age
  change raw = _ at keyEq
  rw [←keyEq] at occ
  have seen : Passing δ blank accept raw (rounds j (startTerm blank c)) := ⟨_,occ,yes,gate⟩
  obtain ⟨rows,rd,_,correct⟩ := read_sound _ _ _ _ _ _ seen
  refine ⟨raw,j,rows,seen,rd,?_,?_,correct⟩
  · have same := pack_injective (rd.symm.trans (read_written blank before last vs w))
    rw [same]; simp [before,trace_length]
  · have wpos := FiniteCodes.wide (α:=L (Color Q Γ))
    have initSize : k < w := by simp [w,initial,initialRow]; omega
    have header : w ≤ w*(A Q Γ).width := Nat.le_mul_of_pos_right _ (A Q Γ).positive
    simp [raw,payload]; omega


private def maxLeaves (seed : Term) : Nat → Nat
  | 0 => size seed
  | j+1 => max (maxLeaves seed j) (size (rounds (j+1) seed))

private theorem le_maxLeaves (seed : Term) (T : Nat) {j : Nat} (hj : j ≤ T) :
    size (rounds j seed) ≤ maxLeaves seed T := by
  induction T with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact Nat.le_refl _
  | succ T ih =>
    by_cases h : j ≤ T
    · exact Nat.le_trans (ih h) (Nat.le_max_left ..)
    · obtain rfl : j = T+1 := by omega
      exact Nat.le_max_right ..

private theorem wordSize (w : List Bool) : w.length ≤ size (W w) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    change (b::w).length ≤ size (Frames.word Shell.g (b::w))
    rw [Generation.addWord]
    have pos := sizePos (Generation.op b)
    change w.length + 1 ≤ size (Generation.op b) + size (W w); omega

/-- For each prefix length, the same orbit contains a correctly decoded packet
    after any prescribed time. Source length and the time bound are not inputs
    of the seed, native evaluator, gate or packet reader. -/
theorem cofinal_prefix (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) (n T : Nat) :
    ∃ j raw rows, T < j ∧ Passing δ blank (fun _ => true) raw (rounds j (startTerm blank c)) ∧
      readTrace (Q:=Q) blank raw = pack rows ∧ rows.length = n+1 ∧ Correct δ blank c rows := by
  let k := n + maxLeaves (startTerm blank c) T + 1
  obtain ⟨raw,j,rows,found,rd,len,big,correct⟩ :=
    complete_with_padding δ blank (fun _ => true) c n k (by dsimp [k]; omega) rfl
  refine ⟨j,raw,rows,?_,found,rd,len,correct⟩
  obtain ⟨r,occ,_,_⟩ := found
  have tagged : size (W raw) ≤ size (.app (tag raw) r) := by simp [tag,size]; omega
  have fits := Nat.le_trans (wordSize raw) (Nat.le_trans tagged occ.sizeLE)
  by_cases h : T < j
  · exact h
  · have small := le_maxLeaves (startTerm blank c) T (show j ≤ T by omega)
    dsimp [k] at big; omega

/-- A fixed regular tree language detects the existence of a passing packet. -/
theorem regular_detection (δ : Table Q Γ) (blank : Γ) (accept : Q → Bool) :
    Regular (fun t => ∃ raw, Passing δ blank accept raw t) := by
  have eq : (fun t => ∃ raw, Passing δ blank accept raw t) =
      (fun t => ∃ row, report δ blank accept t = some row) := by
    funext t; apply propext; constructor
    · rintro ⟨raw,r,occ,wp,bp⟩
      have hit := (localReport_iff (wordTest δ blank accept) (bodyTest (Q:=Q) (Γ:=Γ))
        (getRow (Q:=Q) blank) (.app (tag raw) r) (getRow (Q:=Q) blank raw)).mpr ⟨_,_,rfl,wp,bp,rfl⟩
      exact first_success _ occ hit
    · rintro ⟨row,h⟩
      obtain ⟨t,occ,hit⟩ := first_sound _ _ _ h
      obtain ⟨raw,r,rfl,wp,bp,_⟩ := (localReport_iff _ _ _ _ _).mp hit
      exact ⟨raw,r,occ,wp,bp⟩
  rw [eq]; exact report_regular ..


/-- Cofinal observations for each source index admit observation times strictly
    increasing with that index. This selects witnesses, not a new evaluator. -/
private theorem ordered_from_cofinal {P : Nat → Nat → Prop}
    (cofinal : ∀ n T, ∃ j, T < j ∧ P n j) :
    ∃ time : Nat → Nat, (∀ n, time n < time (n+1)) ∧ ∀ n, P n (time n) := by
  classical
  let next := fun n T => Classical.choose (cofinal n T)
  have spec (n T) : T < next n T ∧ P n (next n T) := Classical.choose_spec (cofinal n T)
  let time : Nat → Nat := fun k => Nat.rec (motive := fun _ => Nat) (next 0 0) (fun n old => next (n+1) old) k
  refine ⟨time,fun n => (spec (n+1) (time n)).1,?_⟩
  intro n
  cases n with
  | zero => exact (spec 0 0).2
  | succ n => exact (spec (n+1) (time n)).2

/-- A chronological subsequence of the native orbit reveals all source prefixes,
    including those of a source run that never halts. This does not assert
    that every packet hit appears in source order. -/
theorem ordered_observations (δ : Table Q Γ) (blank : Γ) (c : Cfg Q Γ) :
    ∃ time : Nat → Nat, (∀ n, time n < time (n+1)) ∧ ∀ n, ∃ raw rows,
      Passing δ blank (fun _ => true) raw (rounds (time n) (startTerm blank c)) ∧
      readTrace (Q:=Q) blank raw = pack rows ∧ rows.length = n+1 ∧ Correct δ blank c rows := by
  apply ordered_from_cofinal (P := fun n j => ∃ raw rows,
    Passing δ blank (fun _ => true) raw (rounds j (startTerm blank c)) ∧
    readTrace (Q:=Q) blank raw = pack rows ∧ rows.length = n+1 ∧ Correct δ blank c rows)
  intro n T
  obtain ⟨j,raw,rows,late,hit,read,len,correct⟩ := cofinal_prefix δ blank c n T
  exact ⟨j,late,raw,rows,hit,read,len,correct⟩

#print axioms read_sound
#print axioms cofinal_prefix
#print axioms regular_detection
#print axioms ordered_observations
end TwoScans.TraceReadout
