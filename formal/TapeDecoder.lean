import Mathlib.Computability.TuringMachine.ToPartrec

namespace TwoScans.TapeDecoder
open Turing Turing.PartrecToTM2

abbrev Cell := TM2to1.Γ' K' (fun _ => Γ')

def bit? : Γ' → Option Bool
  | .bit0 => some false | .bit1 => some true | _ => none

/-- Extract a finite string in time linear in the supplied tape segment. -/
def digits (r : List Cell) := (r.filterMap (fun c => (c.2 K'.main).bind bit?)).reverse

def binary (y : Nat) := (trNat y).filterMap bit?

private def eraseBlanks (r : ListBlank (Option Γ')) : List Bool :=
  r.liftOn (fun xs => xs.filterMap (fun x => x.bind bit?)) (by
    rintro a _ ⟨n,rfl⟩
    have h : (List.replicate n (none : Option Γ')).filterMap (fun x => x.bind bit?) = [] := by simp
    change _ = (a ++ List.replicate n (none : Option Γ')).filterMap _
    simp only [List.filterMap_append]; rw [h,List.append_nil])

set_option backward.isDefEq.respectTransparency false in
theorem reads (r : List Cell) (L : ListBlank (K' → Option Γ')) (y : Nat)
    (h : TM2to1.addBottom L = ListBlank.mk r)
    (out : L.map (Turing.proj K'.main) = ListBlank.mk ((trList [y]).map some).reverse) :
    digits r = binary y := by
  let sndMap : PointedMap Cell (K' → Option Γ') := ⟨Prod.snd,rfl⟩
  have s : (ListBlank.mk r).map sndMap = L := h ▸ TM2to1.addBottom_map L
  rw [←s] at out
  have e := congrArg eraseBlanks out
  simp only [ListBlank.map_mk] at e
  change ((r.map Prod.snd).map (fun f => f K'.main)).filterMap (fun x => x.bind bit?) =
    ((List.map some (trList [y])).reverse).filterMap (fun x => x.bind bit?) at e
  have l : ((r.map Prod.snd).map (fun f => f K'.main)).filterMap (fun x => x.bind bit?) =
      r.filterMap (fun c => (c.2 K'.main).bind bit?) := by
    rw [List.map_map,List.filterMap_map]; rfl
  have rr : ((List.map some (trList [y])).reverse).filterMap (fun x => x.bind bit?) =
      (binary y).reverse := by
    rw [List.filterMap_reverse,List.filterMap_map]
    congr 1
    simp [binary,bit?]
  rw [l,rr] at e
  exact (congrArg List.reverse e).trans (List.reverse_reverse _)

def value : List Bool → Nat
  | [] => 0 | b::bs => (if b then 1 else 0) + 2*value bs

private theorem value_pos (n : PosNum) : value ((trPosNum n).filterMap bit?) = (n : Nat) := by
  induction n with
  | one => rfl
  | bit0 k ih => simp [trPosNum,bit?,value,ih] ; omega
  | bit1 k ih => simp [trPosNum,bit?,value,ih] ; omega

theorem binary_value (n : Nat) : value (binary n) = n := by
  have numcase (x : Num) : value ((trNum x).filterMap bit?) = (x : Nat) := by
    cases x with
    | zero => rfl
    | pos p => exact value_pos p
  simpa [binary,trNat] using numcase (n : Num)

end TwoScans.TapeDecoder
#print axioms TwoScans.TapeDecoder.reads
#print axioms TwoScans.TapeDecoder.binary_value
