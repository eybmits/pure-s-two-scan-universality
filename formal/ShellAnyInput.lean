import TableauEndToEnd

namespace TwoScans.AnyTape
open Automata WordBlocks TrackLayout PayloadBits Tableau OneTape

inductive Mark (C : Type)
  | data (c : C) | live (c : C) | stop | padding | fence
  deriving DecidableEq
instance {C} [FinStates C] : FinStates (Mark C) :=
  ⟨[.stop,.padding,.fence] ++ FinStates.enum.map .data ++ FinStates.enum.map .live,
   fun m => by cases m <;> simp [FinStates.covers]⟩

def forget (blank wall : C) : Mark C → C
  | .data c | .live c => c
  | .stop | .padding => blank
  | .fence => wall

def markedRule (F : Rule C) (blank wall : C) : Rule (Mark C) :=
  fun l c r => .live (F (l.map (forget blank wall)) (forget blank wall c) (r.map (forget blank wall)))

def initialRow (c : List C) (k : Nat) : List (Mark C) :=
  c.map .data ++ .stop :: (List.replicate k .padding ++ [.fence])

abbrev L (C : Type) := Label (Site (Mark C)) (Option (Mark C))
abbrev ctag (c : C) : L C := .color (some (.data c))
abbrev etag : L C := .color (some .stop)
def key (A : Alphabet (L C)) (core : List C) : List Bool :=
  chunks A ((core.map ctag ++ [etag]).reverse) ++ chunks A [.color none,.vb]

private theorem stem_unique (A : Alphabet (L C)) (x y : List C) (a b : List Bool)
    (e : a ++ chunks A ((x.map ctag ++ [etag]).reverse) =
         b ++ chunks A ((y.map ctag ++ [etag]).reverse)) : x = y := by
  have push {c : C} {cs : List C} : chunks A (((c::cs).map ctag ++ [etag]).reverse) =
     chunks A ((cs.map ctag ++ [etag]).reverse) ++ A.code (ctag c) := by simp [chunks]
  have split {a b : List Bool} {c d : L C} (e : a ++ A.code c = b ++ A.code d) : a=b ∧ c=d := by
    obtain ⟨h,k⟩ := List.append_inj' e ((A.length c).trans (A.length d).symm)
    exact ⟨h,A.faithful _ _ k⟩
  induction x generalizing y a b with
  | nil =>
    cases y with
    | nil => rfl
    | cons v vs =>
      rw [push,←List.append_assoc] at e
      have end0 : chunks A (([].map ctag ++ [etag]).reverse) = A.code etag := by simp [chunks]
      rw [end0] at e; have bad := (split e).2; cases bad
  | cons v vs ih =>
    cases y with
    | nil =>
      rw [push,←List.append_assoc] at e
      have end0 : chunks A (([].map ctag ++ [etag]).reverse) = A.code etag := by simp [chunks]
      rw [end0] at e; have bad := (split e).2; cases bad
    | cons u us =>
      simp only [push,←List.append_assoc] at e
      obtain ⟨he,ce⟩ := split e
      have tags : v = u := by simpa [ctag] using ce
      subst u; exact congrArg (List.cons v) (ih us a b he)

theorem key_unique (A : Alphabet (L C)) (x y : List C) (a b : List Bool)
    (h : a ++ key A x = b ++ key A y) : x = y := by
  simp only [key,←List.append_assoc] at h
  exact stem_unique A _ _ _ _ (List.append_cancel_right h)

theorem genuine_key [DecidableEq C] (A : Alphabet (L C)) (core : List C) (k : Nat)
    (b : List (List (Tile (Mark C)))) (last : List (Mark C)) (vs : List (Option (Mark C))) (w : Nat)
    (head : (b.map (List.map Tile.center) ++ [last]).head? = some (initialRow core k))
    (probes : TrackTests (writeSites b last) vs w) :
    ∃ extra, payload A (writeSites b last) vs w [] = extra ++ key A core := by
  have mirror := ((track_iff_sites b last vs w).1 probes).1
  let tail := (List.replicate k (some (Mark.padding : Mark C))) ++ [some Mark.fence]
  have first : ∃ rest, vs = [none] ++ core.map (some ∘ Mark.data) ++ [some .stop] ++ rest := by
    rw [mirror]
    generalize hr : b.map (List.map Tile.center) ++ [last] = rs at head ⊢
    cases rs with
    | nil => cases head
    | cons r rs =>
      have er : r = initialRow core k := Option.some.inj head
      subst r
      exact ⟨tail ++ pack rs,by simp [initialRow,pack,tail,List.map_map,Function.comp_def,List.append_assoc]⟩
  obtain ⟨rest,ev⟩ := first
  let base : List (L C) := [.vb,.color none] ++ core.map ctag ++ [etag]
  let other : List (L C) := rest.map Label.color ++ [.ve,.ue] ++
    (writeSites b last).reverse.map Label.site ++ [.ub]
  have recode : reverseBody (writeSites b last) vs = base ++ other := by
    simp [reverseBody,ev,base,other,etag,List.map_map,Function.comp_def,List.append_assoc]
  have eb : chunks A base.reverse = key A core := by
    simp [base,key,chunks,List.reverse_append,List.append_assoc]
  have h : bodyLabels (writeSites b last) vs = other.reverse ++ base.reverse := by
    rw [←rev_body,recode,List.reverse_append]
  refine ⟨(List.replicate (w*A.width) true ++ [false]) ++ chunks A other.reverse,?_⟩
  simp only [payload,h,List.append_nil,←eb,chunks,List.flatMap_append,List.append_assoc]

inductive Mode | empty | pad | input | bad deriving DecidableEq
instance : FinStates Mode := ⟨[.empty,.pad,.input,.bad],fun q => by cases q <;> simp⟩
def readIn : Mark C → Mode → Mode
  | .fence,.empty => .pad
  | .padding,.pad => .pad
  | .stop,.pad => .input
  | .data _,.input => .input
  | _,_ => .bad
def inOK (m : Mode) := decide (m = .input)

private def meaning (r : List (Mark C)) : Mode → Prop
  | .empty => r = []
  | .pad => ∃ k, r = List.replicate k .padding ++ [.fence]
  | .input => ∃ core k, r = initialRow core k
  | .bad => True
private theorem readMeaning (a : Mark C) (s : Mode) (r : List (Mark C))
    (h : meaning r s) : meaning (a::r) (readIn a s) := by
  cases a <;> cases s <;> try trivial
  case data.input c => obtain ⟨xs,k,rfl⟩ := h; exact ⟨c::xs,k,rfl⟩
  case stop.pad => obtain ⟨k,rfl⟩ := h; exact ⟨[],k,rfl⟩
  case padding.pad => obtain ⟨k,rfl⟩ := h; exact ⟨k+1,by simp [List.replicate_succ]⟩
  case fence.empty => have eq : r = [] := h; subst r; exact ⟨0,rfl⟩

theorem input_iff (r : List (Mark C)) : inOK (r.foldr readIn .empty) = true ↔
   ∃ core k, r = initialRow core k := by
  constructor
  · have H : meaning r (r.foldr readIn .empty) := by
      induction r with | nil => rfl | cons a r ih => exact readMeaning _ _ _ ih
    intro z; rw [show r.foldr readIn .empty = .input from of_decide_eq_true z] at H; exact H
  · rintro ⟨xs,k,rfl⟩
    have pad (n) : ((List.replicate n .padding ++ [.fence]) : List (Mark C)).foldr readIn .empty = .pad := by
      induction n with | zero => rfl | succ n ih => simp only [List.replicate_succ,List.cons_append,List.foldr_cons,ih]; rfl
    have core (x : List C) : (initialRow x k).foldr readIn .empty = .input := by
      induction x with
      | nil => change readIn .stop _ = _; rw [pad]; rfl
      | cons a xs ih => change readIn (.data a) ((initialRow xs k).foldr readIn .empty) = _; rw [ih]; rfl
    rw [core]; rfl

end TwoScans.AnyTape
