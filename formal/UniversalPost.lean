import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine.ToPartrec

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace TwoScans.UniversalPost
open Turing Denumerable Encodable
open Turing.PartrecToTM2

/-- One fixed partial-recursive program evaluates every Mathlib Gödel code
    on every numeric input. In particular, the program does not depend on the
    machine being emulated. -/
theorem universalCode : ∃ u : ToPartrec.Code, ∀ (c : Nat.Partrec.Code) (x : Nat),
    u.eval [encode c,x] = (c.eval x).map (fun y => [y]) := by
  let f := fun n x : Nat => (ofNat Nat.Partrec.Code n).eval x
  have hf : Partrec₂ f :=
    Nat.Partrec.Code.eval_part.comp ((Computable.ofNat _).comp Computable.fst) Computable.snd
  obtain ⟨u,h⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₂.mpr hf)
  refine ⟨u,fun c x => ?_⟩
  let v : List.Vector Nat 2 := ⟨[encode c,x],rfl⟩
  have hv := h v
  change u.eval [encode c,x] = (f (encode c) x).map _ at hv
  rw [show (pure : Nat → List Nat) = (fun y => [y]) from rfl] at hv
  simpa [f] using hv

abbrev Cell := TM2to1.Γ' K' (fun _ => Γ')
abbrev State := TM1to0.Λ' (TM2to1.tr tr)

def tapeInput (c : Nat.Partrec.Code) (x : Nat) : List Cell :=
  TM2to1.trInit K'.main (trList [encode c,x])

def Outputs (t : ListBlank Cell) (y : Nat) :=
  ∃ L : ListBlank (K' → Option Γ'), TM2to1.addBottom L = t ∧
    L.map (Turing.proj K'.main) = ListBlank.mk ((trList [y]).map some).reverse

private theorem stack_init (u : ToPartrec.Code) (ns) :
    letI : Inhabited Λ' := ⟨trNormal u Cont'.halt⟩
    TM2.init K'.main (trList ns) = PartrecToTM2.init u ns := by
  unfold TM2.init PartrecToTM2.init
  congr 1
  funext k
  cases k <;> rfl

private theorem stack_result (u : ToPartrec.Code) (ns) :
    letI : Inhabited Λ' := ⟨trNormal u Cont'.halt⟩
    TM2.eval tr K'.main (trList ns) = (u.eval ns).map trList := by
  unfold TM2.eval
  rw [stack_init u ns, PartrecToTM2.tr_eval]
  rw [Part.map_eq_map,Part.map_map]
  rfl

private theorem domain (u : ToPartrec.Code) (ns : List Nat) :
    letI : Inhabited Λ' := ⟨trNormal u Cont'.halt⟩
    (TM0.eval (TM1to0.tr (TM2to1.tr tr)) (TM2to1.trInit K'.main (trList ns))).Dom ↔ (u.eval ns).Dom := by
  letI : Inhabited Λ' := ⟨trNormal u Cont'.halt⟩
  exact (Iff.of_eq (congrArg Part.Dom (TM1to0.tr_eval (TM2to1.tr tr) _))).trans
    ((TM2to1.tr_eval_dom tr K'.main _).trans (Iff.of_eq (congrArg Part.Dom (stack_result u ns))))

private theorem output (u : ToPartrec.Code) (ns : List Nat) (y : Nat) (t : ListBlank Cell)
    (hy : [y] ∈ u.eval ns) :
    letI : Inhabited Λ' := ⟨trNormal u Cont'.halt⟩
    t ∈ TM0.eval (TM1to0.tr (TM2to1.tr tr)) (TM2to1.trInit K'.main (trList ns)) → Outputs t y := by
  letI : Inhabited Λ' := ⟨trNormal u Cont'.halt⟩
  intro ht
  have hTM1 : t ∈ TM1.eval (TM2to1.tr tr) (TM2to1.trInit K'.main (trList ns)) :=
    (Iff.of_eq (congrArg (fun z : Part (ListBlank Cell) => t ∈ z) (TM1to0.tr_eval (TM2to1.tr tr) (TM2to1.trInit K'.main (trList ns))))).mp ht
  have hstack : trList [y] ∈ TM2.eval tr K'.main (trList ns) := by
    rw [stack_result u ns]
    exact (Part.mem_map_iff _).mpr ⟨[y],hy,rfl⟩
  obtain ⟨S,L,eq,hL,out⟩ := TM2to1.tr_eval tr K'.main _ hTM1 hstack
  exact ⟨L,eq,by simpa only [out] using hL K'.main⟩

/-- A fixed Post machine with a single finite support, exact universal domain,
    and the actual result encoded in the main tape track whenever it halts. -/
theorem universalPost : ∃ (start : State) (M : @TM0.Machine Cell State ⟨start⟩) (support : Finset State),
    @TM0.Supports _ _ ⟨start⟩ M support ∧
    (∀ (c : Nat.Partrec.Code) (x : Nat),
      (@TM0.eval Cell State ⟨start⟩ _ M (tapeInput c x)).Dom ↔ (c.eval x).Dom) ∧
    (∀ (c : Nat.Partrec.Code) (x y : Nat) (t : ListBlank Cell),
      y ∈ c.eval x → t ∈ @TM0.eval Cell State ⟨start⟩ _ M (tapeInput c x) → Outputs t y) := by
  obtain ⟨u,hu⟩ := universalCode
  letI : Inhabited Λ' := ⟨trNormal u Cont'.halt⟩
  let M := TM1to0.tr (TM2to1.tr tr)
  let support := TM1to0.trStmts (TM2to1.tr tr) (TM2to1.trSupp tr (codeSupp u Cont'.halt))
  refine ⟨(default : TM1to0.Λ' (TM2to1.tr tr)),M,support,?_,?_,?_⟩
  · exact TM1to0.tr_supports _ (TM2to1.tr_supports _ (tr_supports u Cont'.halt))
  · intro c x
    exact (domain u [encode c,x]).trans (Iff.of_eq (congrArg Part.Dom (hu c x)))
  · intro c x y t hy ht
    have ok : [y] ∈ u.eval [encode c,x] := by
      rw [hu]; exact (Part.mem_map_iff _).mpr ⟨y,hy,rfl⟩
    exact output u _ y t ok ht

#print axioms universalPost
end TwoScans.UniversalPost
