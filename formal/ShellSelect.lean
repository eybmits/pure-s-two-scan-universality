import ShellOutput

namespace TwoScans.Select
open Term Automata Shell

/-- The annotation preserves tree shape and stores a finite state at each
    node. A representation may retain a pointer to the underlying node. -/
inductive Decor (Q : Type) where
  | leaf (q : Q)
  | fork (q : Q) (left right : Decor Q)

def Decor.state {Q} : Decor Q → Q | .leaf q => q | .fork q _ _ => q
def Decor.erase {Q} : Decor Q → Term
  | .leaf _ => s
  | .fork _ l r => app l.erase r.erase

def decorate {Q} (a : Fold Q) : Term → Decor Q
  | s => .leaf a.leaf
  | .app l r =>
    let lc := decorate a l
    let rc := decorate a r
    .fork (a.fork lc.state rc.state) lc rc

theorem decoration_state {Q} (a : Fold Q) (t : Term) : (decorate a t).state = a.run t := by
  induction t with
  | s => rfl
  | app l r il ir => change a.fork _ _ = a.fork _ _; rw [il,ir]

@[simp] theorem decoration_erase {Q} (a : Fold Q) (t : Term) : (decorate a t).erase = t := by
  induction t with
  | s => rfl
  | app l r il ir => change app _ _ = app _ _; rw [il,ir]

def marks {Q} (a : Fold Q) (yes : Q → Bool) : Fold (Q × Bool) :=
  a.extend (yes a.leaf) (fun l r => yes (a.fork l.1 r.1) || l.2 || r.2)

theorem mark_below {Q} (a : Fold Q) (yes : Q → Bool) (t : Term) :
    ((marks a yes).run t).2 = true ↔ ∃ u, Occ u t ∧ yes (a.run u) = true := by
  induction t with
  | s =>
    change yes (a.run s) = true ↔ _
    constructor
    · intro ok; exact ⟨_,.here,ok⟩
    · rintro ⟨_,o,ok⟩; cases o; exact ok
  | app l r il ir =>
    let f := marks a yes
    change (yes (a.fork (f.run l).1 (f.run r).1) || (f.run l).2 || (f.run r).2) = true ↔ _
    rw [show (f.run l).1 = _ from Fold.extend_base ..,show (f.run r).1 = _ from Fold.extend_base ..]
    change (yes (a.run (app l r)) || ((marks a yes).run l).2 || ((marks a yes).run r).2) = true ↔ _
    rw [Bool.or_eq_true,Bool.or_eq_true,il,ir]
    constructor
    · rintro ((ok | ⟨_,o,ok⟩) | ⟨_,o,ok⟩)
      · exact ⟨_,.here,ok⟩
      · exact ⟨_,.left o,ok⟩
      · exact ⟨_,.right o,ok⟩
    · rintro ⟨_,o,ok⟩; cases o with
      | here => exact .inl (.inl ok)
      | left o => exact .inl (.inr ⟨_,o,ok⟩)
      | right o => exact .inr ⟨_,o,ok⟩

def select {Q} (yes : Q → Bool) : Decor (Q × Bool) → Option (Decor (Q × Bool))
  | v@(.leaf q) => if yes q.1 then some v else none
  | v@(.fork q l r) =>
    if yes q.1 then some v
    else if l.state.2 then select yes l else if r.state.2 then select yes r else none

def visits {Q} (yes : Q → Bool) : Decor (Q × Bool) → Nat
  | .leaf _ => 1
  | .fork q l r => 1 + if yes q.1 then 0 else if l.state.2 then visits yes l else if r.state.2 then visits yes r else 0

def depth {Q} : Decor Q → Nat
  | .leaf _ => 1
  | .fork _ l r => 1 + max (depth l) (depth r)

theorem visits_le_depth {Q} (yes : Q → Bool) (v : Decor (Q × Bool)) :
    visits yes v ≤ depth v := by
  induction v with
  | leaf _ => exact Nat.le_refl _
  | fork q l r il ir =>
    simp only [visits,depth]
    have hl := Nat.le_max_left (depth l) (depth r)
    have hr := Nat.le_max_right (depth l) (depth r)
    split <;> try omega
    split <;> try omega
    split <;> omega

def nodeCount : Term → Nat | s => 1 | .app l r => nodeCount l + nodeCount r + 1
def decorationCalls : Term → Nat | s => 1 | .app l r => 1 + decorationCalls l + decorationCalls r

theorem calls_exact (t : Term) : decorationCalls t = nodeCount t := by
  induction t with | s => rfl | app l r il ir => simp [decorationCalls,nodeCount,il,ir]; omega

theorem depth_le_nodes {Q} (a : Fold Q) (t : Term) :
    depth (decorate a t) ≤ nodeCount t := by
  induction t with
  | s => exact Nat.le_refl _
  | app l r il ir => simp [depth,decorate,nodeCount]; omega

theorem some_first_iff {Q Y : Type} (a : Fold Q) (yes : Q → Bool) (read : Term → Option Y)
    (correct : ∀ t, yes (a.run t) = true ↔ ∃ y, read t = some y) (t) :
    ((marks a yes).run t).2 = true ↔ ∃ y, first read t = some y := by
  rw [mark_below]
  constructor
  · rintro ⟨u,o,ok⟩; obtain ⟨y,hy⟩ := (correct _).mp ok; exact first_success read o hy
  · rintro ⟨y,h⟩; obtain ⟨u,o,ok⟩ := first_sound _ _ _ h; exact ⟨_,o,(correct _).mpr ⟨_,ok⟩⟩

theorem select_correct {Q Y : Type} (a : Fold Q) (yes : Q → Bool) (read : Term → Option Y)
    (correct : ∀ t, yes (a.run t) = true ↔ ∃ y, read t = some y) (t) :
    (select yes (decorate (marks a yes) t)).bind (fun v => read v.erase) = first read t := by
  let f := marks a yes
  have no (v : Term) (e : (f.run v).2 = false) : first read v = none := by
    cases h : first read v with
    | none => rfl
    | some y =>
      have h' := (some_first_iff a yes read correct v).mpr ⟨y,h⟩
      rw [e] at h'; cases h'
  induction t with
  | s =>
    change (if yes a.leaf then some (Decor.leaf (f.leaf)) else none).bind _ = read s
    cases e : read s with
    | none =>
      have reject : yes a.leaf = false := by
        cases h : yes a.leaf with | false => rfl | true => obtain ⟨y,hy⟩ := (correct s).1 h; rw [e] at hy; cases hy
      simp [reject]
    | some y => have ok := (correct s).2 ⟨y,e⟩; change yes a.leaf = true at ok; simp [ok,Decor.erase,e]
  | app l r il ir =>
    change (if yes ((decorate f (app l r)).state.1) then some (decorate f (app l r)) else
      if (decorate f l).state.2 then select yes (decorate f l) else
      if (decorate f r).state.2 then select yes (decorate f r) else none).bind _ =
      (read (app l r)).or ((first read l).or (first read r))
    rw [decoration_state, show (f.run (app l r)).1 = _ from Fold.extend_base ..,decoration_state,decoration_state]
    cases et : read (app l r) with
    | some z =>
      have ok := (correct _).2 ⟨_,et⟩
      simp [ok,et]
    | none =>
      have reject : yes (a.run (app l r)) = false := by
        cases h : yes (a.run (app l r)) with | false => rfl | true => obtain ⟨y,hy⟩ := (correct _).1 h; rw [et] at hy; cases hy
      simp only [reject,Bool.false_eq_true,ite_false,Option.none_or]
      cases el : (f.run l).2 with
      | true =>
        obtain ⟨z,ez⟩ := (some_first_iff a yes read correct l).mp el
        simpa [el,f,ez] using il
      | false =>
        have nl := no l el
        cases er : (f.run r).2 with
        | true => simpa [el,er,nl,f] using ir
        | false => simp [nl,no r er]

theorem regular_local {Y} (wp bp) (v : List Bool → Y)
    (row : Regular (fun t => ∃ w, t = W w ∧ wp w = true))
    (route : Regular (fun t => bp t = true)) :
    Regular (fun t => ∃ y, localReport wp bp v t = some y) := by
  obtain ⟨Q,i,a,p,h⟩ := regular_app (regular_app (regular_exact marker) row) route
  refine ⟨Q,i,a,p,?_⟩
  intro t; rw [h]
  constructor
  · rintro ⟨_,r,rfl,⟨_,_,rfl,rfl,w,rfl,hw⟩,hr⟩
    exact ⟨_,(localReport_iff _ _ _ _ _).mpr ⟨w,r,rfl,hw,hr,rfl⟩⟩
  · rintro ⟨y,hy⟩
    obtain ⟨w,r,rfl,hw,hr,_⟩ := (localReport_iff _ _ _ _ _).mp hy
    exact ⟨_,_,rfl,⟨_,_,rfl,rfl,w,rfl,hw⟩,hr⟩

/-- A single bottom-up finite annotation plus one root-to-node walk produces
    the exact first shell on all raw trees, including malformed inputs.
    The bound counts tree visits before the selected payload's output pass. -/
theorem linear_selection {Y} (wp bp) (v : List Bool → Y)
    (row : Regular (fun t => ∃ w, t = W w ∧ wp w = true))
    (route : Regular (fun t => bp t = true)) :
    ∃ (Q : Type) (_ : FinStates Q) (a : Fold Q) (yes : Q → Bool), ∀ t,
       (select yes (decorate (marks a yes) t)).bind (fun node => localReport wp bp v node.erase)
         = first (localReport wp bp v) t ∧
       decorationCalls t + visits yes (decorate (marks a yes) t) ≤ 2 * nodeCount t := by
  obtain ⟨Q,i,a,yes,h⟩ := regular_local wp bp v row route
  refine ⟨Q,i,a,yes,fun t => ⟨select_correct a yes _ h t,?_⟩⟩
  have hv := visits_le_depth yes (decorate (marks a yes) t)
  have hd := depth_le_nodes (marks a yes) t
  rw [calls_exact]; omega

#print axioms linear_selection
#print axioms select_correct
#print axioms visits_le_depth
end TwoScans.Select
