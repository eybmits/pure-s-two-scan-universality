import Tableau

/- The two native reads are now represented as the colors at two aligned
   positions. Each tile check itself depends on a bounded window. The only
   occurrence of the displacement in the checker is the semantic lookup
   that stands for the calibrated native read. -/
namespace TwoScans.Tableau
variable {C : Type}

structure Tile (C : Type) where
  left : Option C
  center : C
  right : Option C
  next : C
deriving DecidableEq, Repr

abbrev Rule (C : Type) := Option C → C → Option C → C

/-- The leftmost distinguished wall is implicit. Exterior/left-neighbor
color for the first represented cell is none; the last represented cell
may be a designated right wall. -/
def sweep (δ : Rule C) (prev : Option C) : List C → List C
  | [] => []
  | c :: cs => δ prev c cs.head? :: sweep δ (some c) cs

@[simp] theorem sweep_length (δ : Rule C) (prev : Option C) (r : List C) :
    (sweep δ prev r).length = r.length := by
  induction r generalizing prev with
  | nil => rfl
  | cons c cs ih => simp [sweep, ih]

def tileCheck [DecidableEq C] (δ : Rule C) (prev : Option C) : List (Tile C) → Bool
  | [] => true
  | t :: ts => decide (t.left = prev ∧ t.right = ts.head?.map Tile.center ∧
      t.next = δ t.left t.center t.right) && tileCheck δ (some t.center) ts

theorem tile_sound [DecidableEq C] (δ : Rule C) (p : Option C) (r : List (Tile C))
    (h : tileCheck δ p r = true) :
    r.map Tile.next = sweep δ p (r.map Tile.center) := by
  induction r generalizing p with
  | nil => rfl
  | cons t ts ih =>
    simp only [tileCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hh := h.1
    rcases hh with ⟨hp, hr, hn⟩
    simp only [List.map_cons, sweep, List.head?_map]
    exact List.cons.injEq _ _ _ _ |>.mpr ⟨by simpa [hp, hr] using hn, ih _ h.2⟩

def tiles (δ : Rule C) (prev : Option C) : List C → List (Tile C)
  | [] => []
  | c :: cs => ⟨prev, c, cs.head?, δ prev c cs.head?⟩ :: tiles δ (some c) cs

@[simp] theorem tiles_center (δ : Rule C) (p : Option C) (r : List C) :
    (tiles δ p r).map Tile.center = r := by
  induction r generalizing p with
  | nil => rfl
  | cons c cs ih => simp [tiles, ih]

@[simp] theorem tiles_pass [DecidableEq C] (δ : Rule C) (p : Option C) (r : List C) :
    tileCheck δ p (tiles δ p r) = true := by
  induction r generalizing p with
  | nil => rfl
  | cons c cs ih =>
    simp only [tiles, tileCheck, ih, Bool.and_true, decide_eq_true_eq, true_and, and_true]
    rw [← List.head?_map, tiles_center]

@[simp] theorem tiles_next [DecidableEq C] (δ : Rule C) (p : Option C) (r : List C) :
    (tiles δ p r).map Tile.next = sweep δ p r := by
  simpa using tile_sound δ p (tiles δ p r) (tiles_pass δ p r)

@[simp] theorem pack_length_map {A : Type} (rows : List (List A)) (f : A → C) :
    (pack (rows.map (List.map f))).length = (pack rows).length := by
  induction rows with
  | nil => rfl
  | cons r rs ih => simp [pack, ih]

@[simp] theorem pack_append (a b : List (List C)) : pack (a ++ b) = pack a ++ pack b := by
  induction a with
  | nil => rfl
  | cons r rs ih => simp [pack, ih]

/-- Compare each delayed read with its expected color. Out-of-range is
represented by the outer none, distinct from the left wall (some none). -/
def sites [DecidableEq C] (flat expected : List (Option C)) (w : Nat) : Bool :=
  (List.range flat.length).all fun i => decide (flat[w+i]? = expected[i]?)

theorem sites_iff [DecidableEq C] (flat expected : List (Option C)) (w : Nat)
    (hlen : expected.length ≤ flat.length) :
    sites flat expected w = true ↔ flat.drop w = expected := by
  simp only [sites, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_drop]
    by_cases hi : i < flat.length
    · exact h i hi
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro h i _
    simpa using congrArg (fun (l : List (Option C)) => l[i]?) h

/-- A fixed radius-one machine supplies the finite palette. Here the candidate
is already split at its one terminal row, wall positions and block boundaries.
The initial row comes from the anchored input and right blank padding. -/
def siteCheck [DecidableEq C] (δ : Rule C) (initial : List C)
    (before : List (List (Tile C))) (last : List C) (w : Nat) : Bool :=
  let rows := before.map (List.map Tile.center) ++ [last]
  decide (w > 0 ∧ rows.head? = some initial) &&
    before.all (tileCheck δ none) &&
    sites (pack rows) (pack (before.map (List.map Tile.next))) w

theorem siteCheck_sound [DecidableEq C] (δ : Rule C) (initial : List C)
    (before : List (List (Tile C))) (last : List C) (w : Nat)
    (pass : siteCheck δ initial before last w = true) :
    last = run (sweep δ none) initial before.length := by
  simp only [siteCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at pass
  obtain ⟨⟨⟨hw, hh⟩, ht⟩, hs⟩ := pass
  have hd := (sites_iff _ _ _ (by simp)).mp hs
  have hp : before.map (List.map Tile.next) =
      (before.map (List.map Tile.center)).map (sweep δ none) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    exact tile_sound _ _ r (ht _ hr)
  rw [hp] at hd
  have checkPass : check (sweep δ none) initial (before.map (List.map Tile.center)) last w = true :=
    decide_eq_true ⟨hw, hh, hd⟩
  simpa using check_sound _ _ _ _ _ checkPass

theorem siteCheck_complete [DecidableEq C] (δ : Rule C) (initial : List C) (n : Nat) :
    siteCheck δ initial ((trace (sweep δ none) initial n).map (tiles δ none))
       (run (sweep δ none) initial n) (initial.length + 1) = true := by
  let step := sweep δ none
  let rs := trace step initial n
  have hh : (rs.map (tiles δ none)).map (List.map Tile.center) = rs := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [ih]
  have hn : (rs.map (tiles δ none)).map (List.map Tile.next) = rs.map step := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [ih, step]
  have hc := check_complete step initial n
  change check step initial rs (run step initial n) (initial.length + 1) = true at hc
  simp only [check, decide_eq_true_eq] at hc
  change siteCheck δ initial (rs.map (tiles δ none)) (run step initial n) _ = _
  simp only [siteCheck, hh, hn, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨hc.1, hc.2.1⟩, ?_⟩, ?_⟩
  · intro r hr
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hr
    apply tiles_pass
  · apply (sites_iff _ _ _ ?_).mpr hc.2.2
    rw [← hc.2.2]
    simp

#print axioms sites_iff
#print axioms siteCheck_sound
#print axioms siteCheck_complete
end TwoScans.Tableau
