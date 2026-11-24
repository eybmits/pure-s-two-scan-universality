import Mathlib.Computability.TuringMachine.PostTuringMachine
import TableauIO

namespace TwoScans.FoldedTape
open Turing Tableau.OneTape

variable {Γ Λ : Type} [Inhabited Γ]
abbrev Pair (Γ : Type) := Γ × Γ
abbrev Column (Γ : Type) := Bool × Pair Γ
abbrev Control (Λ : Type) := Option Λ × Bool
def clear : Column Γ := (false,(default,default))

/-- Two tape tracks are folded at the cut between integer positions -1 and 0.
    True denotes the nonnegative track. The marker on the first column
    makes crossing the physical boundary a stationary, track-changing step. -/
def lane (pos : Bool) (c : Pair Γ) := if pos then c.1 else c.2
def store (pos : Bool) (x : Γ) (c : Pair Γ) : Pair Γ := if pos then (x,c.2) else (c.1,x)

structure Strip (Γ : Type) where
  left : List (Pair Γ)
  here : Pair Γ
  right : List (Pair Γ)

def outside (d : Strip Γ) : Strip Γ := match d.right with
  | [] => ⟨d.here::d.left,(default,default),[]⟩
  | a::as => ⟨d.here::d.left,a,as⟩
def inside (d : Strip Γ) : Strip Γ := match d.left with
  | [] => d
  | a::as => ⟨as,a,d.here::d.right⟩

def mark : List (Pair Γ) → List (Column Γ)
  | [] => []
  | x::xs => (xs.isEmpty,x):: mark xs

def physical (q : Option Λ) (side : Bool) (d : Strip Γ) : Cfg (Control Λ) (Column Γ) :=
  ⟨mark d.left,(q,side),(d.left.isEmpty,d.here),d.right.map (fun a => (false,a))⟩

def view (pos : Bool) (d : Strip Γ) : Tape Γ :=
  let long := ListBlank.mk (d.left.map (lane pos) ++ d.left.reverse.map (lane (!pos)) ++
    lane (!pos) d.here :: d.right.map (lane (!pos)))
  let short := ListBlank.mk (d.right.map (lane pos))
  if pos then ⟨lane pos d.here,long,short⟩ else ⟨lane pos d.here,short,long⟩

@[simp] private theorem blankEnd (l : List Γ) : ListBlank.mk (l ++ [default]) = ListBlank.mk l := by
  exact Quotient.sound' (Or.inr ⟨1,rfl⟩)

@[simp] private theorem mkApp (l : List Γ) (a : Γ) (k : List Γ) :
    ListBlank.mk (l ++ a :: k ++ [default]) = ListBlank.mk (l ++ a :: k) := blankEnd _

@[simp] private theorem out_pos (d : Strip Γ) :
    view true (outside d) = (view true d).move .right := by
  rcases d with ⟨l,h,r⟩; cases r <;>
    simp [outside,view,Tape.move,lane,ListBlank.head_mk,ListBlank.tail_mk,ListBlank.cons_mk,
      -List.reverse_append,List.append_assoc]
  · simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
      blankEnd (h.1 :: (l.map (lane true) ++ ((l.map (lane false)).reverse ++ [h.2])))

@[simp] private theorem out_neg (d : Strip Γ) :
    view false (outside d) = (view false d).move .left := by
  rcases d with ⟨l,h,r⟩; cases r <;>
    simp [outside,view,Tape.move,lane,ListBlank.head_mk,ListBlank.tail_mk,ListBlank.cons_mk,
      -List.reverse_append,List.append_assoc]
  · simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
      blankEnd (h.2 :: (l.map (lane false) ++ ((l.map (lane true)).reverse ++ [h.1])))

private theorem crossing (pos : Bool) (d : Strip Γ) :
    view (if d.left.isEmpty then !pos else pos) (inside d) =
      (view pos d).move (if pos then .left else .right) := by
  rcases d with ⟨l,h,r⟩; cases l <;> cases pos <;>
    simp [inside,view,Tape.move,lane,ListBlank.head_mk,ListBlank.tail_mk,ListBlank.cons_mk,
      List.append_assoc]

@[simp] private theorem store_view (pos : Bool) (x : Γ) (d : Strip Γ) :
    view pos {d with here := store pos x d.here} = (view pos d).write x := by
  cases pos <;> rfl

/-- One ordinary semi-infinite transition per Post action; an extra stationary
    transition converts a source stop instruction into the explicit halt state. -/
def table [Inhabited Λ] (M : TM0.Machine Γ Λ) : Table (Control Λ) (Column Γ) :=
  fun (q,pos) (first,a) => match q with
    | none => ⟨(none,pos),(first,a),.stay⟩
    | some q => match M q (lane pos a) with
      | none => ⟨(none,pos),(first,a),.stay⟩
      | some (q',.write x) => ⟨(some q',pos),(first,store pos x a),.stay⟩
      | some (q',.move d) =>
        let away := match d with | .left => !pos | .right => pos
        if away then ⟨(some q',pos),(first,a),.right⟩ else
        if first then ⟨(some q',!pos),(first,a),.stay⟩ else ⟨(some q',pos),(first,a),.left⟩

private theorem out_step {q':Λ} (pos : Bool) (d : Strip Γ) :
    let c := physical (some q') pos d
    (match c.right with
      | [] => Cfg.mk (c.here::c.left) (some q',pos) clear []
      | a::as => ⟨c.here::c.left,(some q',pos),a,as⟩) = physical (some q') pos (outside d) := by
  rcases d with ⟨l,h,r⟩; cases r <;> simp [physical,outside,mark,clear]

theorem simulate [Inhabited Λ] (M : TM0.Machine Γ Λ) (q : Λ) (pos : Bool) (d : Strip Γ) :
    match TM0.step M ⟨q,view pos d⟩ with
    | none => advance (table M) clear (physical (some q) pos d) = physical none pos d
    | some dest => ∃ side d',
      advance (table M) clear (physical (some q) pos d) = physical (some dest.q) side d' ∧
      view side d' = dest.Tape := by
  have head : (view pos d).head = lane pos d.here := by cases pos <;> rfl
  simp only [TM0.step,head]
  cases step : M q (lane pos d.here) with
  | none => simp [advance,table,physical,step]
  | some z =>
    rcases z with ⟨q',act⟩
    cases act with
    | write x =>
      refine ⟨pos,{d with here := store pos x d.here},?_,store_view ..⟩
      simp [advance,table,physical,step]
    | move dir =>
      cases dir <;> cases pos
      case left.false => exact ⟨false,outside d,by rcases d with ⟨l,h,r⟩; cases r <;> simp_all [advance,table,physical,outside,mark,clear],out_neg d⟩
      case right.true => exact ⟨true,outside d,by rcases d with ⟨l,h,r⟩; cases r <;> simp_all [advance,table,physical,outside,mark,clear],out_pos d⟩
      case left.true =>
        refine ⟨if d.left.isEmpty then false else true,inside d,?_,crossing true d⟩
        rcases d with ⟨l,h,r⟩; cases l <;> simp_all [advance,table,physical,inside,mark]
      case right.false =>
        refine ⟨if d.left.isEmpty then true else false,inside d,?_,crossing false d⟩
        rcases d with ⟨l,h,r⟩; cases l <;> simp_all [advance,table,physical,inside,mark]

#print axioms simulate
end TwoScans.FoldedTape
