import TrackLayout
import TableauIO

namespace TwoScans.Tableau
variable {C : Type}

/-- Finite letters in the U track. Final cells omit unused successor fields. -/
inductive Site (C : Type)
  | row | cell (t : Tile C) | finalRow | finalCell (c : C)
  deriving DecidableEq, Repr

def Site.current : Site C → Option C
  | .row | .finalRow => none
  | .cell t => some t.center
  | .finalCell c => some c

def Site.expected : Site C → Option (Option C)
  | .row => some none
  | .cell t => some (some t.next)
  | .finalRow | .finalCell _ => none

def preSites (r : List (Tile C)) : List (Site C) := .row :: r.map .cell
def finalSites (r : List C) : List (Site C) := .finalRow :: r.map .finalCell
def writeSites (before : List (List (Tile C))) (last : List C) : List (Site C) :=
  before.flatMap preSites ++ finalSites last

@[simp] theorem current_flat_pre (before : List (List (Tile C))) :
    (before.flatMap preSites).map Site.current = pack (before.map (List.map Tile.center)) := by
  induction before with
  | nil => rfl
  | cons r rs ih =>
    simp [preSites, pack, ih, List.map_map, Site.current, Function.comp_def]

@[simp] theorem current_write (before : List (List (Tile C))) (last : List C) :
    (writeSites before last).map Site.current =
    pack (before.map (List.map Tile.center) ++ [last]) := by
  simp [writeSites, finalSites, pack, List.map_map, Site.current, Function.comp_def]

@[simp] theorem expect_nonfinal (before : List (List (Tile C))) :
    (before.flatMap preSites).map Site.expected =
      (pack (before.map (List.map Tile.next))).map some := by
  induction before with
  | nil => rfl
  | cons r rs ih =>
    simp [preSites, pack, ih, List.map_map, Site.expected, Function.comp_def]

private theorem expected_final (last : List C) (j : Nat) (hj : j < (finalSites last).length) : (finalSites last)[j].expected = none := by
  cases j <;> simp [finalSites, Site.expected]

@[simp] theorem expected_at (before : List (List (Tile C))) (last : List C)
    (i : Nat) (hi : i < (writeSites before last).length) :
    (writeSites before last)[i].expected = (pack (before.map (List.map Tile.next)))[i]? := by
  let pre := before.flatMap preSites
  have hlen : (pack (before.map (List.map Tile.next))).length = pre.length := by
    simpa only [List.length_map,pre] using (congrArg List.length (expect_nonfinal before)).symm
  by_cases hp : i < pre.length
  · have h := congrArg (fun (l : List (Option (Option C))) => l[i]?) (expect_nonfinal before)
    have hpp : i < (pack (before.map (List.map Tile.next))).length := by omega
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < (before.flatMap preSites).length from hp),
      List.getElem?_eq_getElem hpp, Option.map_some, Option.some.injEq] at h
    unfold writeSites at hi ⊢
    rw [List.getElem_append_left (show i < (before.flatMap preSites).length from hp), List.getElem?_eq_getElem hpp]
    exact h
  · simp only [writeSites, List.getElem_append_right (show (before.flatMap preSites).length ≤ i from Nat.le_of_not_gt hp),
      List.getElem?_eq_none (show (pack (before.map (List.map Tile.next))).length ≤ i from by omega)]
    exact expected_final _ _ _

/-- End, fast-site and delayed-site observations on decoded labels, with no
assumption that the proposed V colors are the claimed mirror. -/
def TrackTests (us : List (Site C)) (vs : List (Option C)) (w : Nat) : Prop :=
  let b := TrackLayout.reverseBody us vs
  b[us.length+1]? = some .ve ∧
    (∀ i (hi : i < us.length), TrackLayout.readColor b[i+1]? = some us[i].current) ∧
    (∀ i (hi : i < us.length), TrackLayout.readColor b[i+w+1]? = us[i].expected)

theorem track_iff_sites [DecidableEq C] (before : List (List (Tile C))) (last : List C)
    (vs : List (Option C)) (w : Nat) :
    TrackTests (writeSites before last) vs w ↔
      vs = pack (before.map (List.map Tile.center) ++ [last]) ∧
      sites vs (pack (before.map (List.map Tile.next))) w = true := by
  let us := writeSites before last
  have sameLen : us.length = (pack (before.map (List.map Tile.center) ++ [last])).length := by
    simpa only [List.length_map, us] using congrArg List.length (current_write before last)
  constructor
  · rintro ⟨finish, fast, slow⟩
    obtain ⟨mirror, align⟩ := TrackLayout.two_tracks Site.current w finish fast
    have hmid := mirror.trans (current_write before last)
    refine ⟨hmid, ?_⟩
    simp only [sites, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    intro i hi
    have h : i < us.length := by simpa only [mirror, List.length_map,us] using hi
    rw [Nat.add_comm]
    exact (congrArg (fun (l : List (Option C)) => l[i+w]?) mirror).trans
      ((align i).symm.trans ((slow i h).trans (expected_at before last i h)))
  · rintro ⟨mirror, pass⟩
    have hm : vs = us.map Site.current := mirror.trans (current_write before last).symm
    have hl : vs.length = us.length := by simp [hm]
    simp only [sites, List.all_eq_true, List.mem_range, decide_eq_true_eq] at pass
    refine ⟨(TrackLayout.end_unique us vs _).mpr hl.symm, ?_, ?_⟩
    · intro i hi
      rw [TrackLayout.color_at,hm, List.getElem?_map, List.getElem?_eq_getElem (show i < us.length from hi)]
      rfl
    · intro i hi
      rw [TrackLayout.color_at, Nat.add_comm, pass i (hl ▸ hi : i < vs.length), expected_at]

theorem tableau_tracks_sound [DecidableEq C] (δ : Rule C) (initial : List C)
    (before : List (List (Tile C))) (last : List C) {vs : List (Option C)} {w : Nat}
    (hw : 0 < w)
    (head : (before.map (List.map Tile.center) ++ [last]).head? = some initial)
    (loc : ∀ r ∈ before, tileCheck δ none r = true)
    (probes : TrackTests (writeSites before last) vs w) :
    siteCheck δ initial before last w = true := by
  rcases (track_iff_sites before last vs w).mp probes with ⟨rfl,h⟩
  simpa only [siteCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using And.intro (And.intro (And.intro hw head) loc) h

theorem tableau_tracks_complete [DecidableEq C] (δ : Rule C) (initial : List C)
    (before : List (List (Tile C))) (last : List C) {w : Nat}
    (h : siteCheck δ initial before last w = true) :
    0 < w ∧ (before.map (List.map Tile.center) ++ [last]).head? = some initial ∧
    (∀ r ∈ before, tileCheck δ none r = true) ∧
    TrackTests (writeSites before last) ((writeSites before last).map Site.current) w := by
  simp only [siteCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2,(track_iff_sites _ _ _ _).mpr
    ⟨current_write _ _,by simpa only [current_write] using h.2⟩⟩

#print axioms tableau_tracks_sound
#print axioms tableau_tracks_complete
end TwoScans.Tableau
