import StringCoding
import UniversalPost
import FoldedRun

namespace TwoScans.BinaryInput
open Turing PartrecToTM2 TapeDecoder UniversalPost StringCoding

def digit : Bool → Γ' | false => .bit0 | true => .bit1

private theorem digits_inv_pos (z : PosNum) : ((trPosNum z).filterMap bit?).map digit = trPosNum z := by
  induction z with
  | one => rfl
  | bit0 z ih => simp [trPosNum,bit?,digit,ih]
  | bit1 z ih => simp [trPosNum,bit?,digit,ih]

theorem digits_inv (n : Nat) : (binary n).map digit = trNat n := by
  change ((trNum (n : Num)).filterMap bit?).map digit = trNum _
  cases (n : Num) with
  | zero => rfl
  | pos z => exact digits_inv_pos z

/-- Externally supplied code bits use the ordinary low-order-first binary
    representation of the Gödel number. The input bits are arbitrary. -/
def program (c : Nat.Partrec.Code) := binary (Encodable.encode c)
def col (bottom : Bool) (a : Γ') : UniversalPost.Cell :=
  (bottom, fun k => match k with | K'.main => some a | _ => none)

/-- Single-pass construction from the two raw bit strings. There is no program
    decoding or potentially unbounded numeric calculation in this function. -/
def tape (p x : List Bool) : List UniversalPost.Cell :=
  col true .cons :: col false .bit1 ::
    (x.reverse.map (fun b => col false (digit b)) ++
    col false .cons :: p.reverse.map (fun b => col false (digit b)))

theorem tape_size (p x : List Bool) : (tape p x).length = p.length+x.length+3 := by
  simp [tape]; omega

private theorem mk_cell (b : Bool) (a : Γ') :
    (b,Function.update (fun _ : K' => none) K'.main (some a)) = col b a := by
  unfold col
  congr 1; funext k; cases k <;> rfl

theorem source_tape (c : Nat.Partrec.Code) (x : List Bool) :
    tape (program c) x = tapeInput c (pack x) := by
  have pc := digits_inv (Encodable.encode c)
  have xi := digits_inv (pack x)
  rw [binary_pack] at xi
  have rev : (trList [Encodable.encode c,pack x]).reverse =
      Γ'.cons :: Γ'.bit1 :: (x.reverse.map digit ++ Γ'.cons :: (program c).reverse.map digit) := by
    simp only [trList,←pc,←xi,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,List.map_append,List.map_cons,List.map_nil,
      List.append_assoc,List.map_reverse,program,digit]
    simp
  unfold tapeInput TM2to1.trInit
  rw [rev]
  simp only [List.map_cons,List.map_append,List.map_map,List.headI_cons,List.tail_cons,
    mk_cell,tape,Function.comp_def]
  rfl

theorem folded_symbol_count (p x : List Bool) {Q : Type} [Inhabited Q] :
    let c := FoldedTape.start (Λ := Q) (tape p x)
    c.left.length + 1 + c.right.length = p.length+x.length+3 := by
  simp [FoldedTape.start,FoldedTape.physical,FoldedTape.stripInput,FoldedTape.mark,tape]
  omega

#print axioms source_tape
#print axioms folded_symbol_count
end TwoScans.BinaryInput
