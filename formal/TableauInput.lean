import TableauTrackIO
import HeaderBlocks

namespace TwoScans.Tableau.OneTape
open WordBlocks TrackLayout HeaderBlocks

inductive Symbol (Z : Type)
  | start | bit (b : Bool) | inputEnd | blank | outputBit (b : Bool) | work (z : Z)
  deriving DecidableEq, Repr
variable {Q Z : Type}

def initial (q : Q) (x : List Bool) : Cfg Q (Symbol Z) :=
  ⟨[],q,.start,x.map .bit ++ [.inputEnd]⟩

def mark : Symbol Z → Option Bool
  | .outputBit b => some b
  | _ => none

abbrev Cell (Q Z : Type) := Color Q (Symbol Z)
abbrev Letter (Q Z : Type) := Label (Site (Cell Q Z)) (Option (Cell Q Z))
def bitCell (b : Bool) : Option (Cell Q Z) := some (.plain (.bit b))
def endCell : Option (Cell Q Z) := some (.plain .inputEnd)
def inputPrefix (q : Q) (x : List Bool) : List (Option (Cell Q Z)) :=
  none :: some (.head q .start) :: (x.map bitCell ++ [endCell])

/-- Rear-first labels of the anchored packet, starting at the rear boundary. -/
def inputKey (q : Q) (x : List Bool) : List (Letter Q Z) :=
  .vb :: (inputPrefix q x).map .color

/-- Wrapper suffix, before the constant footer. -/
def anchor (A : Alphabet (Letter Q Z)) (q : Q) (x : List Bool) :=
  chunks A (inputKey q x).reverse

private theorem split_code {α : Type} (A : Alphabet α) {p r : List Bool} {x y : α}
    (h : p ++ A.code x = r ++ A.code y) : p = r ∧ x = y := by
  obtain ⟨e,f⟩ := List.append_inj' h ((A.length x).trans (A.length y).symm)
  exact ⟨e,A.faithful x y f⟩

private def bitLabel (b : Bool) : Letter Q Z := .color (bitCell b)
private def endLabel : Letter Q Z := .color endCell
private def stem (A : Alphabet (Letter Q Z)) (x : List Bool) : List Bool :=
  chunks A ((x.map bitLabel ++ [endLabel]).reverse)

private theorem stem_nil (A : Alphabet (Letter Q Z)) : stem A [] = A.code endLabel := by
  simp [stem,chunks]
private theorem stem_cons (A : Alphabet (Letter Q Z)) (b) (x) :
    stem A (b::x) = stem A x ++ A.code (bitLabel b) := by
  simp [stem,chunks,List.append_assoc]

private theorem stem_unique (A : Alphabet (Letter Q Z)) (x y : List Bool)
    (p r : List Bool) (e : p ++ stem A x = r ++ stem A y) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b bs =>
      rw [stem_nil,stem_cons,←List.append_assoc] at e
      have he := (split_code A e).2
      cases he
  | cons a as ih =>
    cases y with
    | nil =>
      rw [stem_cons,stem_nil,←List.append_assoc] at e
      have he := (split_code A e).2
      cases he
    | cons b bs =>
      rw [stem_cons,stem_cons,←List.append_assoc,←List.append_assoc] at e
      obtain ⟨rest,biteq⟩ := split_code A e
      have bits : a = b := by simpa [bitLabel,bitCell] using biteq
      subst b
      exact congrArg (List.cons a) (ih bs rest)

private theorem anchor_stem (A : Alphabet (Letter Q Z)) (q : Q) (x : List Bool) :
    anchor A q x = stem A x ++ chunks A
      ([.vb, .color none, .color (some (.head q .start))] : List (Letter Q Z)).reverse := by
  simp [anchor,inputKey,inputPrefix,chunks,stem,endLabel,List.map_map,Function.comp_def,
    List.append_assoc]
  rfl

/-- No two binary inputs can appear as anchored suffixes of one word, even
if their lengths and the other left contexts are unrelated. -/
theorem anchor_unique (A : Alphabet (Letter Q Z)) (q : Q) (x y : List Bool)
    (p r foot : List Bool)
    (h : (p ++ anchor A q x) ++ foot = (r ++ anchor A q y) ++ foot) : x = y := by
  have h := List.append_cancel_right h
  rw [anchor_stem, anchor_stem, ←List.append_assoc, ←List.append_assoc] at h
  exact stem_unique A x y p r (List.append_cancel_right h)

theorem mirror_starts_with_input (q : Q) (x : List Bool) (k : Nat)
    (rows : List (List (Cell Q Z)))
    (head : rows.head? = some (encode (pad .blank (initial q x) k))) :
    ∃ extra, pack rows = inputPrefix q x ++ extra := by
  cases rows with
  | nil => simp at head
  | cons r rs =>
    simp only [List.head?_cons, Option.some.injEq] at head
    subst r
    refine ⟨(List.replicate k (some (.plain .blank))) ++ [some .wall] ++ pack rs, ?_⟩
    simp [pack, inputPrefix, initial, encode, pad, bitCell, endCell,
      List.map_map, Function.comp_def, List.append_assoc]

/-- Every correctly mirrored static first row contributes exactly its
unambiguous input suffix to the full binary payload. A possibly unaligned
initial header and any constant footer do not affect the assertion. -/
theorem real_anchor (A : Alphabet (Letter Q Z)) (q : Q) (x : List Bool) (k : Nat)
    (us : List (Site (Cell Q Z))) (vs : List (Option (Cell Q Z))) (w : Nat)
    (before : List (List (Tile (Cell Q Z)))) (last : List (Cell Q Z))
    (hLayout : us = writeSites before last)
    (head : (before.map (List.map Tile.center) ++ [last]).head? =
      some (encode (pad .blank (initial q x) k)))
    (probes : TrackTests us vs w) (hdr foot : List Bool) :
    ∃ other, BlockWire.wire A hdr foot (reverseBody us vs) = (other ++ anchor A q x) ++ foot := by
  rcases probes with ⟨finish,fast,_⟩
  obtain ⟨hm,_⟩ := two_tracks Site.current w finish fast
  obtain ⟨extra,he⟩ := mirror_starts_with_input q x k _ head
  have hsv : vs = inputPrefix q x ++ extra := by rw [hm,hLayout,current_write,he]
  have hb : reverseBody us vs = inputKey q x ++
      (extra.map .color ++ [.ve,.ue] ++ us.reverse.map .site ++ [.ub]) := by
    simp [reverseBody,hsv,inputKey,List.append_assoc]
  let rest : List (Letter Q Z) := extra.map .color ++ [.ve,.ue] ++ us.reverse.map .site ++ [.ub]
  refine ⟨hdr ++ chunks A rest.reverse, ?_⟩
  change (hdr ++ chunks A (reverseBody us vs).reverse) ++ foot = _
  change reverseBody us vs = inputKey q x ++ rest at hb
  rw [hb,List.reverse_append]
  simp only [anchor,chunks,List.flatMap_append,List.append_assoc]

#print axioms anchor_unique
#print axioms real_anchor
end TwoScans.Tableau.OneTape
