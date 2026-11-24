import Anchors

namespace TwoScans.Automata
open Term

/-- A finite state space with an exhaustive table. Repetitions are allowed. -/
class FinStates (Q : Type) where
  enum : List Q
  covers : ∀ q, q ∈ enum

instance : FinStates Bool := ⟨[false,true],fun q => by cases q <;> simp⟩
instance : FinStates Unit := ⟨[()],fun q => by cases q; simp⟩
instance (n : Nat) : FinStates (Fin n) := ⟨List.finRange n,List.mem_finRange⟩
instance {A B} [FinStates A] [FinStates B] : FinStates (A × B) :=
  ⟨(FinStates.enum (Q:=A)).flatMap (fun a => (FinStates.enum (Q:=B)).map (fun b => (a,b))),
   fun (a,b) => List.mem_flatMap.mpr ⟨a,FinStates.covers a,List.mem_map.mpr ⟨b,FinStates.covers b,rfl⟩⟩⟩
instance {A} [FinStates A] : FinStates (Option A) :=
  ⟨none :: (FinStates.enum (Q:=A)).map some,fun q => by
    cases q with
    | none => simp
    | some a => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,FinStates.covers a,rfl⟩)⟩

def tables {A B : Type} [DecidableEq A] [FinStates B] [Inhabited B] :
    List A → List (A → B)
  | [] => [fun _ => default]
  | a :: tail => (tables tail).flatMap (fun g =>
      FinStates.enum.map (fun y x => if x = a then y else g x))

theorem tables_cover {A B : Type} [DecidableEq A] [FinStates B] [Inhabited B]
    (domain : List A) (f : A → B) :
    ∃ g ∈ tables domain, ∀ x ∈ domain, g x = f x := by
  induction domain with
  | nil => exact ⟨_,List.mem_singleton_self _,fun x h => by cases h⟩
  | cons a rest ih =>
    obtain ⟨g,hg,agrees⟩ := ih
    refine ⟨fun x => if x = a then f a else g x, List.mem_flatMap.mpr
      ⟨g,hg,List.mem_map.mpr ⟨f a,FinStates.covers _,rfl⟩⟩,?_⟩
    intro x hx
    by_cases eq : x = a
    · subst x; simp
    · simpa [eq] using agrees x ((List.mem_cons.mp hx).resolve_left eq)

instance {A B : Type} [DecidableEq A] [FinStates A] [FinStates B] [Inhabited B] :
    FinStates (A → B) :=
  ⟨tables FinStates.enum,fun f => by
    obtain ⟨g,hg,e⟩ := tables_cover FinStates.enum f
    rwa [show g = f from funext (fun x => e x (FinStates.covers x))] at hg⟩

structure Fold (Q : Type) where
  leaf : Q
  fork : Q → Q → Q

def Fold.run {Q} (a : Fold Q) : Term → Q
  | s => a.leaf
  | .app l r => a.fork (a.run l) (a.run r)

def Regular (P : Term → Prop) :=
  ∃ (Q : Type) (_ : FinStates Q) (a : Fold Q) (accept : Q → Bool),
    ∀ t, accept (a.run t) = true ↔ P t

def Fold.zip {A B} (a : Fold A) (b : Fold B) : Fold (A × B) :=
  ⟨(a.leaf,b.leaf),fun x y => (a.fork x.1 y.1,b.fork x.2 y.2)⟩

theorem Fold.zip_run {A B} (a : Fold A) (b : Fold B) (t) :
    (a.zip b).run t = (a.run t,b.run t) := by
  induction t with
  | s => rfl
  | app l r il ir => simp only [Fold.run,il,ir]; rfl

/-- Extend a simultaneous bottom-up calculation with one state field. -/
def Fold.extend {A B} (base : Fold A) (start : B) (branch : (A × B) → (A × B) → B) :
    Fold (A × B) :=
  ⟨(base.leaf,start),fun l r => (base.fork l.1 r.1,branch l r)⟩

theorem Fold.extend_base {A B} (base : Fold A) (start : B) (branch) (t) :
    ((base.extend start branch).run t).1 = base.run t := by
  induction t with
  | s => rfl
  | app l r il ir =>
    change base.fork _ _ = base.fork _ _
    rw [il,ir]

theorem regular_leaf : Regular (· = s) := by
  let a : Fold Bool := ⟨true,fun _ _ => false⟩
  exact ⟨Bool,inferInstance,a,id,fun t => by cases t <;> simp [a,Fold.run]⟩

/-- Require predicates on the immediate left and right child, respectively. -/
theorem regular_app {P R} (hp : Regular P) (hr : Regular R) :
    Regular (fun t => ∃ l r, t = app l r ∧ P l ∧ R r) := by
  obtain ⟨A,ia,a,pa,ha⟩ := hp
  obtain ⟨B,ib,b,pb,hb⟩ := hr
  let f : Fold ((A × B) × Bool) :=
    (a.zip b).extend false (fun l r => pa l.1.1 && pb r.1.2)
  haveI := ia
  haveI := ib
  refine ⟨_,inferInstance,f,Prod.snd,?_⟩
  intro t
  cases t with
  | s => simp [f,Fold.run,Fold.extend]
  | app l r =>
    change (pa ((f.run l).1.1) && pb ((f.run r).1.2)) = true ↔ _
    rw [show (f.run l).1 = _ from Fold.extend_base ..,show (f.run r).1 = _ from Fold.extend_base ..,
        Fold.zip_run,Fold.zip_run]
    simp only [Bool.and_eq_true,ha,hb]
    constructor
    · exact fun ⟨hl,hr⟩ => ⟨l,r,rfl,hl,hr⟩
    · rintro ⟨a,b,e,hp,hr⟩; cases e; exact ⟨hp,hr⟩

theorem regular_exact (u : Term) : Regular (· = u) := by
  induction u with
  | s => exact regular_leaf
  | app l r il ir =>
    obtain ⟨Q,inst,a,p,h⟩ := regular_app il ir
    exact ⟨Q,inst,a,p,fun t => by rw [h]; simp⟩

theorem regular_somewhere {P} (hp : Regular P) :
    Regular (fun t => ∃ u, Occ u t ∧ P u) := by
  obtain ⟨Q,iq,a,p,h⟩ := hp
  haveI := iq
  let f := a.extend (p a.leaf) (fun l r => p (a.fork l.1 r.1) || l.2 || r.2)
  refine ⟨_,inferInstance,f,Prod.snd,?_⟩
  intro t
  induction t with
  | s =>
    change p (a.run s) = true ↔ _
    rw [h]
    constructor
    · intro hs; exact ⟨s,.here,hs⟩
    · rintro ⟨u,o,hu⟩; cases o; exact hu
  | app l r il ir =>
    change (p (a.fork (f.run l).1 (f.run r).1) || (f.run l).2 || (f.run r).2) = true ↔ _
    rw [show (f.run l).1 = _ from Fold.extend_base ..,show (f.run r).1 = _ from Fold.extend_base ..]
    change (p (a.run (app l r)) || (f.run l).2 || (f.run r).2) = true ↔ _
    rw [Bool.or_eq_true,Bool.or_eq_true,h,il,ir]
    constructor
    · rintro ((top | ⟨u,o,hu⟩) | ⟨u,o,hu⟩)
      · exact ⟨_,.here,top⟩
      · exact ⟨_,.left o,hu⟩
      · exact ⟨_,.right o,hu⟩
    · rintro ⟨u,o,hu⟩
      cases o with
      | here => exact .inl (.inl hu)
      | left ol => exact .inl (.inr ⟨_,ol,hu⟩)
      | right orr => exact .inr ⟨_,orr,hu⟩
end TwoScans.Automata
