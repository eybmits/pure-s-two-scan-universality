import SupportedPost
import UniversalPost

set_option linter.style.haveILetI false
namespace TwoScans.FiniteUniversalPost
open Turing UniversalPost SupportedPost Automata
open PartrecToTM2

/-- The library gives the four stack indices definitionally; enumerate them
explicitly to obtain the finite universal tape alphabet. -/
instance finiteStackIndex : Fintype K' :=
  ⟨{.main,.rev,.aux,.stack}, fun k => by cases k <;> simp⟩

instance cellFintype : Fintype UniversalPost.Cell :=
  TM2to1.Γ'.fintype

private instance : FinStates K' := ⟨[.main,.rev,.aux,.stack],fun k => by cases k <;> simp⟩
private instance : FinStates Γ' := ⟨[.consₗ,.cons,.bit0,.bit1],fun a => by cases a <;> simp⟩

instance cellStates : FinStates UniversalPost.Cell := inferInstanceAs (FinStates (Bool × (K' → Option Γ')))

instance cellDecEq : DecidableEq UniversalPost.Cell := fun a b =>
  decidable_of_iff (a.1 = b.1 ∧ a.2 .main = b.2 .main ∧ a.2 .rev = b.2 .rev ∧
    a.2 .aux = b.2 .aux ∧ a.2 .stack = b.2 .stack) (by
      constructor
      · rintro ⟨h,m,r,x,s⟩
        exact Prod.ext h (funext fun i => by cases i <;> assumption)
      · rintro rfl; exact ⟨rfl,rfl,rfl,rfl,rfl⟩)

/-- One genuinely finite set of labels for all program/input pairs, without
any run-time support assumption. The result includes the actual output tape. -/
theorem finite_universal :
    ∃ (P : Type) (_ : FinStates P) (_ : DecidableEq P) (q : P) (M : @TM0.Machine UniversalPost.Cell P ⟨q⟩),
      (∀ (c : Nat.Partrec.Code) (x : Nat),
        (@TM0.eval UniversalPost.Cell P ⟨q⟩ _ M (tapeInput c x)).Dom ↔ (c.eval x).Dom) ∧
      (∀ (c : Nat.Partrec.Code) (x y : Nat) (t : ListBlank UniversalPost.Cell),
        y ∈ c.eval x → t ∈ @TM0.eval UniversalPost.Cell P ⟨q⟩ _ M (tapeInput c x) → Outputs t y) := by
  classical
  obtain ⟨q,M,s,hs,dom,out⟩ := universalPost
  letI : Inhabited UniversalPost.State := ⟨q⟩
  letI : Inhabited s := start hs
  refine ⟨s,finiteStates _,Classical.decEq _,default,restrict M s hs,?_,?_⟩
  · intro c x
    rw [same_eval M s hs]
    exact dom c x
  · intro c x y t hsrc ht
    rw [same_eval M s hs] at ht
    exact out c x y t hsrc ht

#print axioms finite_universal
end TwoScans.FiniteUniversalPost
