import TableauTracks
import ShellWordAutomata

namespace TwoScans.Static
open Tableau Automata

variable {C Q : Type}

/-- Semantic parser used only in the correctness proof. -/
inductive Parsed (C : Type) where
  | bad
  | tail (last : List C)
  | full (before : List (List (Tile C))) (last : List C)
  | part (t : Tile C) (more : List (Tile C)) (before : List (List (Tile C))) (last : List C)

def parseStep : Site C → Parsed C → Parsed C
  | .finalCell c, .tail cs => .tail (c :: cs)
  | .finalRow, .tail cs => .full [] cs
  | .row, .full bs cs => .full ([] :: bs) cs
  | .row, .part t ts bs cs => .full ((t :: ts) :: bs) cs
  | .cell t, .full bs cs => .part t [] bs cs
  | .cell t, .part t' ts bs cs => .part t (t'::ts) bs cs
  | _, _ => .bad

def parse (ss : List (Site C)) := ss.foldr parseStep (.tail [])

def reprint : Parsed C → List (Site C)
  | .bad => []
  | .tail cs => cs.map .finalCell
  | .full bs cs => writeSites bs cs
  | .part t ts bs cs => (t::ts).map .cell ++ writeSites bs cs

theorem parse_inverse (ss : List (Site C)) (ok : parse ss ≠ .bad) :
    reprint (parse ss) = ss := by
  induction ss with
  | nil => rfl
  | cons a ss ih =>
    change reprint (parseStep a (parse ss)) = a :: ss
    change parseStep a (parse ss) ≠ .bad at ok
    generalize e : parse ss = v at ok ⊢
    cases a <;> cases v <;> simp [parseStep] at ok
    all_goals try contradiction
    all_goals have tail := ih (by rw [e]; intro h; cases h)
    all_goals rw [e] at tail
    all_goals rw [← tail]
    all_goals first | rfl | simp [parseStep,reprint,writeSites,preSites,List.append_assoc]

private theorem parse_final (last : List C) :
    (last.map Site.finalCell).foldr parseStep (.tail []) = .tail last := by
  induction last with
  | nil => rfl
  | cons c cs ih => simp [ih,parseStep]

private theorem parse_cells (r : List (Tile C)) (bs : List (List (Tile C))) (cs : List C) :
    (r.map Site.cell).foldr parseStep (.full bs cs) =
      match r with
      | [] => .full bs cs
      | t::ts => .part t ts bs cs := by
  induction r with
  | nil => rfl
  | cons t r ih => simp only [List.map_cons,List.foldr_cons,ih]; cases r <;> rfl

theorem parse_write (before : List (List (Tile C))) (last : List C) :
    parse (writeSites before last) = .full before last := by
  induction before with
  | nil => change parseStep .finalRow ((last.map Site.finalCell).foldr parseStep (.tail [])) = _; rw [parse_final]; rfl
  | cons r rs ih =>
    have e : writeSites (r::rs) last = .row :: (r.map Site.cell ++ writeSites rs last) := by simp [writeSites,preSites,List.append_assoc]
    rw [e]
    change parseStep .row (((r.map Site.cell) ++ writeSites rs last).foldr parseStep (.tail [])) = _
    rw [List.foldr_append]
    change parseStep .row ((r.map Site.cell).foldr parseStep (parse (writeSites rs last))) = _
    rw [ih,parse_cells]
    cases r <;> rfl

/-- The actual finite parser retains at most two adjacent tape colors, one
    Boolean and the state of the initial-row word automaton. -/
inductive Phase (C Q : Type) where
  | bad
  | tail (hasHalt : Bool) (initial : Q)
  | full (initial : Q)
  | part (head : C) (left : Option C) (initial : Q)
  deriving DecidableEq

instance [FinStates C] [FinStates Q] : FinStates (Phase C Q) :=
  ⟨[.bad] ++ (FinStates.enum (Q:=Bool × Q)).map (fun (h,q) => .tail h q) ++
       (FinStates.enum (Q:=Q)).map .full ++
       (FinStates.enum (Q:=C × Option C × Q)).map (fun (c,l,q) => .part c l q),
   fun x => by
     cases x with
     | bad => simp
     | tail h q => simp only [List.mem_append]; exact .inl (.inl (.inr (List.mem_map.mpr ⟨(h,q),FinStates.covers _,rfl⟩)))
     | full q => simp only [List.mem_append]; exact .inl (.inr (List.mem_map.mpr ⟨q,FinStates.covers _,rfl⟩))
     | part c l q => simp only [List.mem_append]; exact .inr (List.mem_map.mpr ⟨(c,l,q),FinStates.covers _,rfl⟩)⟩

def advance [DecidableEq C] (δ : Rule C) (halt : C → Bool) (base : Q)
    (input : C → Q → Q) : Site C → Phase C Q → Phase C Q
  | .finalCell c, .tail z q => .tail (halt c || z) (input c q)
  | .finalRow, .tail z q => if z then .full q else .bad
  | .row, .full _ => .full base
  | .row, .part _ p q => if p = none then .full q else .bad
  | .cell t, .full _ => if t.right = none ∧ t.next = δ t.left t.center t.right
      then .part t.center t.left (input t.center base) else .bad
  | .cell t, .part r p q => if t.right = some r ∧ p = some t.center ∧ t.next = δ t.left t.center t.right
      then .part t.center t.left (input t.center q) else .bad
  | _, _ => .bad

def score [DecidableEq C] (δ : Rule C) (halt : C → Bool) (base : Q)
    (input : C → Q → Q) : Parsed C → Phase C Q
  | .bad => .bad
  | .tail cs => .tail (cs.any halt) (cs.foldr input base)
  | .full bs cs =>
    if bs.all (tileCheck δ none) && cs.any halt
    then .full ((bs.head?.map (List.map Tile.center) |>.getD cs).foldr input base) else .bad
  | .part t ts bs cs =>
    if (tileCheck δ t.left (t::ts) && bs.all (tileCheck δ none)) && cs.any halt
    then .part t.center t.left (((t::ts).map Tile.center).foldr input base) else .bad

private theorem cons_check [DecidableEq C] (δ : Rule C) (l : Option C) (t : Tile C) (ts : List (Tile C)) :
    tileCheck δ l (t::ts) = (decide (t.left = l) && tileCheck δ t.left (t::ts)) := by
  simp [tileCheck,Bool.and_assoc]

private theorem score_step [DecidableEq C] (δ : Rule C) (halt : C → Bool) (base : Q)
    (input : C → Q → Q) (s : Site C) (p : Parsed C) :
    score δ halt base input (parseStep s p) = advance δ halt base input s (score δ halt base input p) := by
  cases s <;> cases p <;> try rfl
  case row.full bs cs =>
    cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;>
      simp [score,parseStep,advance,tileCheck,b,h]
  case row.part t ts bs cs =>
    simp only [parseStep,score,List.all_cons]
    simp only [cons_check δ none t ts]
    cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;>
      cases v : tileCheck δ t.left (t::ts) <;> by_cases l : t.left = none <;>
      simp [advance,l]
  case cell.full t bs cs =>
    cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;>
      by_cases r : t.right = none <;> by_cases n : t.next = δ t.left t.center t.right <;>
      simp [score,parseStep,advance,b,h,tileCheck,r,n] at *
  case cell.part t u ts bs cs =>
    cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;>
      cases z : tileCheck δ u.left (u::ts) <;> by_cases r : t.right = some u.center <;>
      by_cases l : u.left = some t.center <;> by_cases n : t.next = δ t.left t.center t.right
    all_goals simp only [parseStep,score,b,h,z,List.map_cons,List.foldr_cons,Bool.and_false,
      Bool.and_true,Bool.false_eq_true,ite_false,ite_true,advance]
    all_goals rw [tileCheck,cons_check δ (some t.center) u ts]
    all_goals simp_all [tileCheck]
  case finalRow.full bs cs => cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;> simp [parseStep,score,b,h,advance]
  case finalCell.full c bs cs => cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;> simp [parseStep,score,b,h,advance]
  case finalRow.part t ts bs cs =>
    cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;>
      cases v : tileCheck δ t.left (t::ts) <;> simp [parseStep,score,b,h,v,advance]
  case finalCell.part c t ts bs cs =>
    cases b : bs.all (tileCheck δ none) <;> cases h : cs.any halt <;>
      cases v : tileCheck δ t.left (t::ts) <;> simp [parseStep,score,b,h,v,advance]
  all_goals simp [parseStep,score,advance]

def done (inputOK : Q → Bool) : Phase C Q → Bool
  | .full q => inputOK q
  | _ => false

theorem score_fold [DecidableEq C] (δ : Rule C) (halt : C → Bool) (base : Q)
    (input : C → Q → Q) (ss : List (Site C)) :
    ss.foldr (advance δ halt base input) (.tail false base) = score δ halt base input (parse ss) := by
  induction ss with
  | nil => rfl
  | cons a ss ih => rw [List.foldr_cons,ih,← score_step]; rfl

/-- Exact finite-state recognition on arbitrary site lists. The explicitly stored
    initial-row automaton is consulted on the first row only. -/
theorem rows_iff [DecidableEq C] (δ : Rule C) (halt : C → Bool) (base : Q)
    (input : C → Q → Q) (inputOK : Q → Bool) (ss : List (Site C)) :
    done inputOK (ss.foldr (advance δ halt base input) (.tail false base)) = true ↔
    ∃ before last, ss = writeSites before last ∧ before.all (tileCheck δ none) = true ∧
      last.any halt = true ∧ inputOK (((before.head?.map (List.map Tile.center)).getD last).foldr input base) = true := by
  rw [score_fold]
  constructor
  · cases e : parse ss with
    | bad => intro h; cases h
    | tail cs => intro h; cases h
    | part t ts bs cs =>
      simp only [score]; split <;> intro h <;> cases h
    | full bs cs =>
      intro ok
      have pp := parse_inverse ss (by rw [e]; intro he; cases he)
      rw [e] at pp
      refine ⟨bs,cs,pp.symm,?_⟩
      simp only [score] at ok
      split at ok
      · rename_i pass; have pair := (show _ ∧ _ from by simpa only [Bool.and_eq_true] using pass)
        exact ⟨pair.1,pair.2,ok⟩
      · cases ok
  · rintro ⟨bs,cs,rfl,rows,halted,first⟩
    rw [parse_write]
    simp [score,rows,halted,done,first]

def outBits (bit : C → Option Bool) (ss : List (Site C)) : List Bool :=
  ss.filterMap (fun | .finalCell c => bit c | _ => none)

theorem bits_write (bit : C → Option Bool) (bs : List (List (Tile C))) (cs : List C) :
    outBits bit (writeSites bs cs) = cs.filterMap bit := by
  have row (ts : List (Tile C)) : outBits bit (preSites ts) = [] := by
    simp [outBits,preSites,List.filterMap_map,Function.comp_def]
  induction bs with
  | nil => simp [outBits,writeSites,finalSites,List.filterMap_map,Function.comp_def]
  | cons r rs ih =>
    have re : writeSites (r::rs) cs = preSites r ++ writeSites rs cs := by simp [writeSites,List.append_assoc]
    simp only [re,outBits,List.filterMap_append]
    change outBits bit (preSites r) ++ outBits bit (writeSites rs cs) = _
    rw [row]; exact ih

#print axioms rows_iff
#print axioms bits_write
end TwoScans.Static
