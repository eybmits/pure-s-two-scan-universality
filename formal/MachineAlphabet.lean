import FiniteCodes
import ObserverClass
import TableauInput
import Shell

namespace TwoScans.MachineAlphabet
open Automata Tableau Tableau.OneTape

instance {Z} [FinStates Z] : FinStates (Symbol Z) where
  enum := [.start,.bit false,.bit true,.inputEnd,.blank,.outputBit false,.outputBit true] ++ FinStates.enum.map .work
  covers x := by
    cases x with
    | bit b | outputBit b => cases b <;> simp
    | work z => simp [FinStates.covers z]
    | _ => simp

instance {Q Γ} [FinStates Q] [FinStates Γ] : FinStates (Color Q Γ) where
  enum := [.wall] ++ FinStates.enum.map .plain ++
    (FinStates.enum (Q := Q × Γ)).map (fun (q,a) => .head q a)
  covers c := by
    cases c with
    | wall => simp
    | plain a => simp [FinStates.covers a]
    | head q a =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨(q,a),FinStates.covers _,rfl⟩

instance {C} [FinStates C] : FinStates (Tile C) where
  enum := (FinStates.enum (Q := Option C × C × Option C × C)).map
    fun (l,c,r,d) => ⟨l,c,r,d⟩
  covers | ⟨l,c,r,d⟩ => List.mem_map.mpr ⟨(l,c,r,d),FinStates.covers _,rfl⟩

instance {C} [FinStates C] : FinStates (Site C) where
  enum := [.row,.finalRow] ++ FinStates.enum.map .cell ++ FinStates.enum.map .finalCell
  covers a := by
    cases a with
    | cell c => simp [FinStates.covers c]
    | finalCell c => simp [FinStates.covers c]
    | _ => simp

def pair : List Bool → List Bool → List Bool
  | [], x => true::x
  | b::p,x => false::b::pair p x

def unpair : List Bool → Option (List Bool × List Bool)
  | true::x => some ([],x)
  | false::b::r => (unpair r).map fun (p,x) => (b::p,x)
  | _ => none

@[simp] theorem unpair_pair (p x : List Bool) : unpair (pair p x) = some (p,x) := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [pair,unpair,ih]

@[simp] theorem pair_len (p x : List Bool) : (pair p x).length = 2*p.length+1+x.length := by
  induction p with
  | nil => simp [pair]; omega
  | cons b p ih => simp [pair,ih]; omega

variable {Q Z : Type} [DecidableEq Q] [DecidableEq Z] [FinStates Q] [FinStates Z]
abbrev alph (Q Z : Type) [DecidableEq Q] [DecidableEq Z] [FinStates Q] [FinStates Z] :=
  FiniteCodes.alphabet (Letter Q Z)

def encodeInput (q : Q) (x : List Bool) : Term :=
  Shell.seed (anchor (alph Q Z) q x)

theorem word_bound (w : List Bool) : size (Shell.W w) ≤ size Shell.g + 1 + 3*w.length := by
  induction w with
  | nil => simp [Shell.W,Frames.word,size]; omega
  | cons c w ih =>
    cases c <;> simp [Shell.W,Frames.word,Frames.A,Frames.B,size] at * <;> omega

theorem encoded_size (q : Q) (x : List Bool) :
    size (encodeInput (Z := Z) q x) ≤ 2*size Shell.g + 1 + 3*((x.length+4)*(alph Q Z).width) := by
  have h := word_bound (anchor (alph Q Z) q x)
  have len : (anchor (alph Q Z) q x).length = (x.length+4)*(alph Q Z).width := by
    simp [anchor,inputKey,inputPrefix]
  rw [len] at h
  change size Shell.g + size (Shell.W _) ≤ _
  omega

end TwoScans.MachineAlphabet
#print axioms TwoScans.MachineAlphabet.encoded_size
