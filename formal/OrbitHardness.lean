import UniversalS
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

set_option linter.style.haveILetI false
namespace TwoScans.OrbitHardness
open Frames Automata UniversalS

/-- The input is a program index together with its numerical argument;
the queried object is the actual pure-S orbit of their encoded ground seed. -/
def Hit (E : Code → Nat → Term) (O : Term → Prop) (cx : Code × Nat) : Prop :=
  ∃ n, O (rounds n (E cx.1 cx.2))

private theorem domainHard (r : Nat → Prop) (hr : REPred r) :
    ManyOneReducible r (fun cx : Code × Nat => (cx.1.eval cx.2).Dom) := by
  let f := fun x => (Part.assert (r x) fun _ => Part.some ()).map (fun _ => (0 : Nat))
  have part : Partrec f := hr.map (Computable.const 0).to₂
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp part)
  refine ⟨fun x => (c,x),(Computable.const c).pair Computable.id,fun x => ?_⟩
  simp [hc,f,Part.assert]

/-- A fixed regular detector has a recursively enumerable complete orbit-hit
problem already on the binary-program/numerical-input family of seeds. Each
r.e. subset of the naturals reduces by a constant program paired with x. -/
theorem concrete_indexed :
    ∃ (P : Type) (fp : FinStates P) (dp : DecidableEq P) (st : Inhabited P)
      (M : @Turing.TM0.Machine Cell P st), letI := fp; letI := dp; letI := st
      let O := fun t => ∃ out, readPost M t = some out
      let ev := Hit (encodePost P) O
      Regular O ∧ REPred ev ∧ ¬ComputablePred ev ∧
      (∀ r : Nat → Prop, REPred r → ManyOneReducible r ev) ∧
      (∀ (c : Code) x, ev (c,x) ↔ (c.eval x).Dom) := by
  obtain ⟨P,fp,dp,st,M,reg,sound,graph⟩ := fixed_machine
  letI := fp; letI := dp; letI := st
  let E := encodePost P
  let O := fun t => ∃ y, readPost M t = some y
  have iffHit (cx : Code × Nat) : Hit E O cx ↔ (cx.1.eval cx.2).Dom := by
    constructor
    · rintro ⟨n,y,h⟩
      obtain ⟨v,hv,_⟩ := sound _ _ _ _ h
      exact hv.1
    · intro dom
      have hv : (cx.1.eval cx.2).get dom ∈ cx.1.eval cx.2 := ⟨dom,rfl⟩
      obtain ⟨n,h⟩ := (graph _ _ _).mpr hv
      exact ⟨n,_,h⟩
  have re : REPred (fun cx : Code × Nat => (cx.1.eval cx.2).Dom) :=
    Nat.Partrec.Code.eval_part.dom_re
  refine ⟨P,fp,dp,st,M,reg,re.of_eq (fun x => (iffHit x).symm),?_,?_,fun c x => iffHit (c,x)⟩
  · intro decided
    apply ComputablePred.halting_problem 0
    apply ComputablePred.computable_of_manyOneReducible (q := Hit E O) _ decided
    exact ⟨fun c => (c,0),Computable.id.pair (Computable.const _),fun c => (iffHit (c,0)).symm⟩
  · intro r hr
    obtain ⟨f,hf,good⟩ := domainHard r hr
    exact ⟨f,hf,fun x => (good x).trans (iffHit _).symm⟩

theorem complete_indexed :
    ∃ (E : Code → Nat → Term) (O : Term → Prop),
      Regular O ∧ REPred (Hit E O) ∧ ¬ ComputablePred (Hit E O) ∧
      (∀ r : Nat → Prop, REPred r → ManyOneReducible r (Hit E O)) ∧
      (∀ (c : Code) x, Hit E O (c,x) ↔ (c.eval x).Dom) := by
  obtain ⟨P,fp,dp,st,M,h⟩ := concrete_indexed
  letI := fp; letI := dp; letI := st
  exact ⟨encodePost P,fun t => ∃ y, readPost M t = some y,h⟩

end TwoScans.OrbitHardness
#print axioms TwoScans.OrbitHardness.concrete_indexed
