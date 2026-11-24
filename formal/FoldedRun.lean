import FoldedTape
import Mathlib.Computability.StateTransition

set_option linter.unusedSectionVars false
namespace TwoScans.FoldedTape
open Turing Tableau Tableau.OneTape StateTransition
variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

def rightList (pos : Bool) (d : Strip Γ) : List Γ :=
  if pos then d.here.1 :: d.right.map Prod.fst
  else d.here.2 :: (d.left.map Prod.snd ++ d.left.reverse.map Prod.fst ++ d.here.1 :: d.right.map Prod.fst)

theorem view_right (pos : Bool) (d : Strip Γ) : ListBlank.mk (rightList pos d) = (view pos d).right₀ := by
  cases pos <;> simp [rightList,view,Tape.right₀,ListBlank.cons_mk,lane] <;> rfl

def unpack (c : Cfg (Control Λ) (Column Γ)) : Strip Γ :=
  ⟨c.left.map Prod.snd, c.here.2,c.right.map Prod.snd⟩

private theorem mark_list (l : List (Pair Γ)) : (mark l).map Prod.snd = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [mark,ih]

theorem unpack_physical (q : Option Λ) (pos : Bool) (d : Strip Γ) :
    unpack (physical q pos d) = d := by
  cases d; simp [unpack,physical,mark_list, List.map_map,Function.comp_def]

def readCfg (c : Cfg (Control Λ) (Column Γ)) := rightList c.state.2 (unpack c)

@[simp] theorem readCfg_physical (q : Option Λ) (pos : Bool) (d : Strip Γ) :
    readCfg (physical q pos d) = rightList pos d := by
  unfold readCfg; rw [unpack_physical]; rfl

private theorem append_blank (l : List Γ) (n : Nat) : ListBlank.mk (l ++ List.replicate n default) = ListBlank.mk l :=
  Quotient.sound' (Or.inr ⟨n,rfl⟩)

theorem pad_readCfg (c : Cfg (Control Λ) (Column Γ)) (n : Nat) :
    ListBlank.mk (readCfg (pad clear c n)) = ListBlank.mk (readCfg c) := by
  have eq : readCfg (pad clear c n) = readCfg c ++ List.replicate n default := by
    rcases c with ⟨l,⟨q,pos⟩,h,r⟩
    cases pos <;> simp [readCfg,unpack,pad,clear,rightList,List.map_map,Function.comp_def,List.append_assoc]
  rw [eq,append_blank]

private def F (M : TM0.Machine Γ Λ) := advance (table M) clear

private theorem fixed_none (M : TM0.Machine Γ Λ) (pos : Bool) (d : Strip Γ) (n : Nat) :
    run (F M) (physical none pos d) n = physical none pos d := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [run, F,advance,table,physical] using ih

private theorem lift_result (M : TM0.Machine Γ Λ) (s z : TM0.Cfg Γ Λ) (hz : z ∈ StateTransition.eval (TM0.step M) s) :
    ∀ pos d, s.Tape = view pos d →
      ∃ n side d', run (F M) (physical (some s.q) pos d) n = physical none side d' ∧ view side d' = z.Tape := by
  apply evalInduction (C := fun src => ∀ pos d, src.Tape = view pos d →
    ∃ n side d', run (F M) (physical (some src.q) pos d) n = physical none side d' ∧ view side d' = z.Tape) hz
  intro source final ih
  
  intro pos d e
  rcases source with ⟨q,t⟩
  change t = _ at e; subst t
  have runOne := simulate M q pos d
  cases h : TM0.step M ⟨q,view pos d⟩ with
  | none =>
    rw [h] at runOne
    have now : (⟨q,view pos d⟩ : TM0.Cfg Γ Λ) ∈ StateTransition.eval (TM0.step M) ⟨q,view pos d⟩ :=
      mem_eval.mpr ⟨.refl,h⟩
    have eq := Part.mem_unique now final
    exact ⟨1,pos,d,runOne,congrArg TM0.Cfg.Tape eq⟩
  | some next =>
    rw [h] at runOne
    obtain ⟨side,d',advance,view'⟩ := runOne
    obtain ⟨n,side',d'',runs,result⟩ := ih next h side d' view'.symm
    refine ⟨n+1,side',d'',?_,result⟩
    change run _ (TwoScans.Tableau.OneTape.advance _ _ _) _ = _
    rw [advance]; exact runs

private theorem lower_result (M : TM0.Machine Γ Λ) (n : Nat) (q : Λ) (pos : Bool) (d : Strip Γ)
    (halted : (run (F M) (physical (some q) pos d) n).state.1.isNone = true) :
    ∃ z ∈ StateTransition.eval (TM0.step M) ⟨q,view pos d⟩,
      z.Tape.right₀ = ListBlank.mk (readCfg (run (F M) (physical (some q) pos d) n)) := by
  induction n generalizing q pos d with
  | zero => cases halted
  | succ n ih =>
    have runOne := simulate M q pos d
    change (run (F M) (advance _ _ _) n).state.1.isNone = true at halted
    change ∃ z : TM0.Cfg Γ Λ, z ∈ StateTransition.eval (TM0.step M) ⟨q,view pos d⟩ ∧ z.Tape.right₀ = ListBlank.mk (readCfg (run (F M) (advance _ _ _) n))
    cases h : TM0.step M ⟨q,view pos d⟩ with
    | none =>
      rw [h] at runOne
      rw [runOne,fixed_none,readCfg_physical,view_right]
      exact ⟨_,mem_eval.mpr ⟨.refl,h⟩,rfl⟩
    | some dest =>
      rw [h] at runOne
      obtain ⟨side,d',advance,view'⟩ := runOne
      rw [advance] at halted ⊢
      obtain ⟨z,hz,eq⟩ := ih _ _ _ halted
      have ev := reaches_eval (Relation.ReflTransGen.single (Option.mem_def.mpr h))
      have src : (⟨dest.q,view side d'⟩ : TM0.Cfg Γ Λ) = dest := by rw [view']
      rw [ev]
      exact ⟨z,src ▸ hz,eq⟩

def stripInput (inp : List Γ) : Strip Γ :=
  ⟨[],(inp.headI,default),inp.tail.map (fun a => (a,default))⟩

theorem view_initial (inp : List Γ) : view true (stripInput inp) = Tape.mk₁ inp := by
  cases inp with
  | nil => exact congrArg (fun x : ListBlank Γ => Tape.mk default x (ListBlank.mk [])) (append_blank [] 1)
  | cons a as =>
    simp [view,stripInput,Tape.mk₁,Tape.mk₂,Tape.mk',ListBlank.head_mk,ListBlank.tail_mk,lane,
      List.map_map,Function.comp_def]
    simpa [List.replicate_succ] using (append_blank ([] : List Γ) (as.length+1))

def start (inp : List Γ) : Cfg (Control Λ) (Column Γ) := physical (some default) true (stripInput inp)

/-- Actual semi-infinite runs have exactly the output domain and values of
    the doubly infinite Post machine. readCfg obtains the inclusive right-hand
    tape as a finite word, with arbitrary trailing blanks ignored. -/
theorem output_iff (M : TM0.Machine Γ Λ) (inp : List Γ) (z : ListBlank Γ) :
    z ∈ TM0.eval M inp ↔ ∃ n, let c := run (advance (table M) clear) (start inp) n
      c.state.1.isNone = true ∧ ListBlank.mk (readCfg c) = z := by
  simp only [TM0.eval,Part.mem_map_iff]
  constructor
  · rintro ⟨conf,m,rfl⟩
    obtain ⟨n,side,d',hn,out⟩ := lift_result M _ conf m true (stripInput inp) (view_initial inp).symm
    refine ⟨n,?_⟩
    change (run (F M) (physical _ true _) n).state.1.isNone = true ∧
      ListBlank.mk (readCfg (run (F M) (physical _ true _) n)) = _
    change run (F M) (physical (some default) true (stripInput inp)) n = _ at hn
    rw [hn,readCfg_physical,view_right,out]; exact ⟨rfl,rfl⟩
  · rintro ⟨n,stop,eq⟩
    obtain ⟨conf,hc,out⟩ := lower_result M n default true (stripInput inp) stop
    rw [view_initial] at hc
    exact ⟨conf,hc,out.trans eq⟩

#print axioms output_iff
#print axioms pad_readCfg
end TwoScans.FoldedTape
