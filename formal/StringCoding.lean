import TapeDecoder
import Mathlib.Computability.PartrecCode

namespace TwoScans.StringCoding
open Turing.PartrecToTM2 TapeDecoder

/-- A final one preserves every trailing zero of the original word. -/
def positive : List Bool → PosNum
  | [] => .one
  | false::bs => .bit0 (positive bs)
  | true::bs => .bit1 (positive bs)

def pack (bs : List Bool) : Nat := (positive bs : Nat)

theorem digits_pos (w : List Bool) :
    (trPosNum (positive w)).filterMap bit? = w ++ [true] := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [positive,trPosNum,bit?] at * <;> exact ih

theorem binary_pack (w : List Bool) : binary (pack w) = w ++ [true] := by
  have h : ((pack w : Nat) : Num) = Num.pos (positive w) := by
    change ((↑(Num.pos (positive w)) : Nat) : Num) = _
    simp
  unfold binary trNat
  rw [h]; exact digits_pos w

theorem injective : Function.Injective pack := by
  intro x y eq
  exact List.append_cancel_right (by simpa only [binary_pack] using congrArg binary eq)

theorem pack_prim : Primrec pack := by
  let step := fun (b : Bool) (n : Nat) => (if b then 1 else 0) + 2*n
  have f : Primrec₂ (fun (_ : List Bool) (a : Bool × Nat) => step a.1 a.2) :=
    (Primrec.nat_add.comp ((Primrec.dom_bool (fun b => if b then 1 else 0)).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂
  apply (Primrec.list_foldr Primrec.id (Primrec.const 1) f).of_eq
  intro w
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [step,pack,positive] at * <;> omega

/-- Search for the inverse is used solely to compile the source program
from the library definition of partial recursiveness. The external decoder
receives bits and removes a single terminal bit. -/
def guess (n k : Nat) : Option (List Bool) :=
  (Encodable.decode (α := List Bool) k).bind (fun w => if pack w = n then some w else none)

theorem guess_comp : Computable₂ guess := by
  unfold guess
  change Computable (fun a : Nat × Nat => (Encodable.decode (α := List Bool) a.2).bind (fun w => if pack w = a.1 then some w else none))
  apply Computable.option_bind (Computable.decode.comp Computable.snd)
  change Computable (fun a : (Nat × Nat) × List Bool => if pack a.2 = a.1.1 then some a.2 else none)
  have h : Primrec (fun a : (Nat × Nat) × List Bool => decide (pack a.2 = a.1.1)) := (Primrec.eq.comp (pack_prim.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).decide
  exact (Computable.cond h.to_comp (Primrec.option_some.to_comp.comp Computable.snd)
    (Computable.const none)).of_eq (fun x => by simp)

theorem found (w : List Bool) : Nat.rfindOpt (guess (pack w)) = Part.some w := by
  have hit : w ∈ guess (pack w) (Encodable.encode w) := by simp [guess,Encodable.encodek]
  have dom := (Nat.rfindOpt_dom).mpr ⟨_,_,hit⟩
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp dom
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hv
  have hvw : v = w := by
    unfold guess at hk
    obtain ⟨z,_,h⟩ := Option.mem_bind_iff.mp hk
    split at h
    next eq => exact (Option.some.inj h).symm.trans (injective eq)
    next => cases h
  subst v
  exact Part.eq_some_iff.mpr hv

theorem program {f : List Bool →. List Bool} (hf : Partrec f) :
    ∃ c : Nat.Partrec.Code, ∀ w, c.eval (pack w) = (f w).map pack := by
  have inv := Partrec.rfindOpt guess_comp
  have hcomp : Partrec (fun n => (Nat.rfindOpt (guess n)).bind (fun w => (f w).map pack)) :=
    inv.bind ((hf.map ((pack_prim.to_comp.comp Computable.snd).to₂)).comp Computable.snd).to₂
  obtain ⟨c,h⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hcomp)
  exact ⟨c,fun w => by rw [h]; simp [found]⟩

end TwoScans.StringCoding
#print axioms TwoScans.StringCoding.program
