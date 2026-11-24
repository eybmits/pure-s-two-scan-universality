import TableauInitialDFA
import ShellOutput

namespace TwoScans.Tableau.Certificate
open WordBlocks TrackLayout PayloadBits Automata OneTape
variable {Q Z : Type} [DecidableEq Q] [DecidableEq Z]

def haltCell (halt : Q → Bool) : Cell Q Z → Bool
  | .head q _ => halt q
  | _ => false
def valueCell : Cell Q Z → Option Bool
  | .plain a | .head _ a => mark a
  | .wall => none

omit [DecidableEq Q] [DecidableEq Z] in
private theorem any_halt (halt : Q → Bool) (r : List (Cell Q Z)) : r.any (haltCell halt) = haltSeen halt r := by
  unfold haltSeen
  apply congrArg (List.any r)
  funext c
  cases c <;> rfl

omit [DecidableEq Q] [DecidableEq Z] in
private theorem read_value (r : List (Cell Q Z)) : r.filterMap valueCell = output mark r := by
  unfold output
  apply congrArg (fun f => r.filterMap f)
  funext c
  cases c <;> rfl

def rowsOK (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q) (u : List (Site (Cell Q Z))) : Bool :=
  Static.done inputAccept (u.foldr (Static.advance (rule δ) (haltCell halt) InputState.empty
    (inputStep q)) (.tail false .empty))

omit [DecidableEq Q] [DecidableEq Z] in
private theorem head_rows (b : List (List (Tile (Cell Q Z)))) (l : List (Cell Q Z)) :
    (b.map (List.map Tile.center) ++ [l]).head? = some ((b.head?.map (List.map Tile.center)).getD l) := by
  cases b <;> rfl

theorem static_iff (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q) (u : List (Site (Cell Q Z))) :
    rowsOK δ halt q u = true ↔ ∃ b l, u = writeSites b l ∧
      (∀ r ∈ b, tileCheck (rule δ) none r = true) ∧
      haltSeen halt l = true ∧ ∃ x k, (b.map (List.map Tile.center) ++ [l]).head? =
        some (encode (pad .blank (initial q x) k)) := by
  unfold rowsOK
  rw [Static.rows_iff]
  simp only [List.all_eq_true, input_iff,head_rows,Option.some.injEq,any_halt]

def Accepted (A : Alphabet (Letter Q Z)) (δ : Table Q (Symbol Z)) (halt : Q → Bool)
    (q : Q) (x y : List Bool) : Prop :=
  ∃ pre u v w, pre ++ anchor A q x = payload A u v w [] ∧
    w > 0 ∧ rowsOK δ halt q u = true ∧ TrackTests u v w ∧ Static.outBits valueCell u = y

omit [DecidableEq Q] [DecidableEq Z] in
private theorem payload_anchor (A : Alphabet (Letter Q Z)) (q : Q) (x : List Bool) (k : Nat)
    (u : List (Site (Cell Q Z))) (v : List (Option (Cell Q Z))) (w : Nat)
    (b : List (List (Tile (Cell Q Z)))) (l : List (Cell Q Z))
    (hu : u = writeSites b l)
    (hh : (b.map (List.map Tile.center) ++ [l]).head? = some (encode (pad .blank (initial q x) k)))
    (pr : TrackTests u v w) :
    ∃ tail, payload A u v w [] = tail ++ anchor A q x := by
  obtain ⟨tail,e⟩ := real_anchor A q x k u v w b l hu hh pr (List.replicate (w*A.width) true ++ [false]) []
  exact ⟨tail,by simpa only [BlockWire.wire,rev_body,List.append_nil,payload,List.append_assoc] using e⟩

/-- The visible V suffix pins the input at the level of actual bits, while
the static input grammar independently permits arbitrary inputs and margins. -/
theorem accepted_iff_tracks (A : Alphabet (Letter Q Z)) (δ : Table Q (Symbol Z)) (halt : Q → Bool)
    (q : Q) (x y : List Bool) :
    Accepted A δ halt q x y ↔ TrackOutput δ .blank halt mark (initial q x) y := by
  constructor
  · rintro ⟨pre,u,v,w,key,hw,staticOk,probes,value⟩
    obtain ⟨b,l,hu,tilesOk,done,z,k,head⟩ := (static_iff _ _ _ _).mp staticOk
    obtain ⟨other,hp⟩ := payload_anchor A q z k u v w b l hu head probes
    have exz : x = z := anchor_unique A q x z pre other [] (by simpa using key.trans hp)
    subst z
    subst u
    rw [Static.bits_write,read_value] at value
    exact ⟨k,b,l,v,w,hw,head,tilesOk,probes,done,value⟩
  · rintro ⟨k,b,l,v,w,hw,head,tilesOk,probes,done,value⟩
    obtain ⟨pre,key⟩ := payload_anchor A q x k (writeSites b l) v w b l rfl head probes
    refine ⟨pre,writeSites b l,v,w,key.symm,hw,(static_iff ..).mpr
      ⟨b,l,rfl,tilesOk,done,x,k,head⟩, probes,?_⟩
    rw [Static.bits_write,read_value]
    exact value

def Computes (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q) (x y : List Bool) : Prop :=
  ∃ n, let c := run (advance (stopped δ halt) .blank) (initial q x) n
       halt c.state = true ∧ output mark (encode c) = y

theorem accepted_iff_computes (A : Alphabet (Letter Q Z)) (δ : Table Q (Symbol Z)) (halt : Q → Bool)
    (q : Q) (x y : List Bool) :
    Accepted A (stopped δ halt) halt q x y ↔ Computes δ halt q x y :=
  (accepted_iff_tracks _ _ _ _ _ _).trans (dual_track_iff_machine_output _ _ _ _ rfl _ _)

theorem computes_unique (δ : Table Q (Symbol Z)) (halt : Q → Bool) (q : Q)
    {x y z : List Bool} (a : Computes δ halt q x y) (b : Computes δ halt q x z) : y = z :=
  unique_track_output δ .blank halt mark rfl (initial q x)
    ((dual_track_iff_machine_output _ _ _ _ rfl _ y).mpr a)
    ((dual_track_iff_machine_output _ _ _ _ rfl _ z).mpr b)

#print axioms accepted_iff_computes
#print axioms computes_unique
end TwoScans.Tableau.Certificate
