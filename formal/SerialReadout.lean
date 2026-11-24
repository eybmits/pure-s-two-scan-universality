import Serial
import ShellAutomata

namespace TwoScans.SerialReadout
open Term Frames Automata SerialTableau

/-- Every post-contraction term, in chronological order, for the first n
    frozen-frontier sweeps. Normal terms add no fictitious stuttering step. -/
def post (e : Term) : Nat → List Term
  | 0 => []
  | n+1 => post e n ++ sweep (rounds n e)

def states (e : Term) (n : Nat) := e :: post e n

theorem prefix_path (e : Term) (n : Nat) : Path e (post e n) (rounds n e) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    rw [rounds_add n 1]
    change Path _ _ (pi (rounds n e))
    rw [←parallel_agrees]; exact ih.append (sweep_is_single_steps _)

theorem one_is_step {a b : Term} (one : One a b) : Step a b := by
  induction one with
  | @root x u h => cases x with | s => cases h | app l r => exact (innermostRoot_sound h).1
  | left r _ ih => exact .left r ih
  | right l _ ih => exact .right l ih

private theorem end_occurs {a z xs} (p : Path a xs z) : z ∈ a :: xs := by
  induction p with | nil => simp | cons _ _ ih => exact .tail _ ih

theorem end_mem (e : Term) (n : Nat) : rounds n e ∈ states e n := end_occurs (prefix_path e n)

theorem rounds_pack (l r : Term) (n) :
    rounds n (pack l r) = pack (rounds n l) (rounds n r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rounds_add n 1,rounds_add n 1 l,rounds_add n 1 r,ih]
    change pi _ = pack (pi _) (pi _)
    simp only [←parallel_agrees,parallel_pack]

theorem first_serial_hit (hit : Term → Bool) (e : Term) (n : Nat) (z : Term)
    (found : (states (pack e e) n).find? (gate hit) = some z) :
    ∃ k c, z = pack (rounds k e) c ∧ hit (rounds k e) = true := by
  induction n with
  | zero =>
    simp only [states,post,List.find?_cons,List.find?_nil] at found
    split at found
    · rename_i yes; cases found
      refine ⟨0,e,rfl,?_⟩
      simpa [pack,gate,rounds] using yes
    · cases found
  | succ n ih =>
    have grow : states (pack e e) (n+1) = states (pack e e) n ++ sweep (pack (rounds n e) (rounds n e)) := by
      simp only [states,post,List.cons_append,rounds_pack]
    rw [grow,List.find?_append] at found
    cases old : (states (pack e e) n).find? (gate hit) with
    | some v => rw [old] at found; cases found; exact ih old
    | none =>
      have veto := List.find?_eq_none.mp old _ (end_mem (pack e e) n)
      rw [rounds_pack] at veto
      have tail : ((pack (rounds n e) (rounds n e)) :: sweep (pack (rounds n e) (rounds n e))).find? (gate hit) = some z := by
        simpa [old,List.find?_cons,veto] using found
      obtain ⟨l,r,eq,h,o⟩ := first_hit_in_sweep hit _ _ tail
      rcases o with rfl | rfl
      · exact ⟨n,r,eq,h⟩
      · have e' : rounds (n+1) e = parallel (rounds n e) := by rw [rounds_add n 1,parallel_agrees]; rfl
        exact ⟨n+1,r,by rw [e']; exact eq,by rw [e']; exact h⟩

def double {Y : Type} (D : Term → Option Y) : Term → Option Y
  | app (app s a) b => if (D b).isSome then D a else none
  | _ => none

theorem double_domain {Y} (D : Term → Option Y) (t) :
    (double D t).isSome = gate (fun v => (D v).isSome) t := by
  cases t with
  | s => rfl
  | app l r =>
    cases l with
    | s => rfl
    | app f x =>
      cases f with
      | app _ _ => rfl
      | s => cases hx : D x <;> cases hr : D r <;> simp [double,gate,hx,hr]

def readFirst {Y : Type} (read : Term → Option Y) (e : Term) (n : Nat) :=
  ((states e n).find? (fun t => (read t).isSome)).bind read

theorem first_from_parallel {Y} (D : Term → Option Y) (e : Term) (n : Nat) {y}
    (h : readFirst (double D) (pack e e) n = some y) : ∃ k, D (rounds k e) = some y := by
  obtain ⟨z,hz,val⟩ := Option.bind_eq_some_iff.mp h
  have gateEq : (fun t => (double D t).isSome) = gate (fun t => (D t).isSome) :=
    funext (double_domain D)
  change (states (pack e e) n).find? (fun t => (double D t).isSome) = some z at hz
  rw [gateEq] at hz
  obtain ⟨k,c,rfl,_⟩ := first_serial_hit _ _ _ _ hz
  have yes := List.find?_some hz
  change ((D (rounds k e)).isSome && (D c).isSome) = true at yes
  have rc := (Bool.and_eq_true_iff.mp yes).2
  exact ⟨k,by simpa [double,pack,rc] using val⟩

theorem parallel_has_first {Y} (D : Term → Option Y) (e : Term) (n : Nat) {y}
    (h : D (rounds n e) = some y) :
    ∃ z, readFirst (double D) (pack e e) n = some z := by
  let ys := states (pack e e) n
  have mem : pack (rounds n e) (rounds n e) ∈ ys := rounds_pack e e n ▸ end_mem (pack e e) n
  let hit := fun t => (double D t).isSome
  have passes : hit (pack (rounds n e) (rounds n e)) = true := by simp [hit,double,pack,h]
  cases seen : ys.find? hit with
  | none => exact False.elim (List.find?_eq_none.mp seen _ mem passes)
  | some v =>
    have yes := List.find?_some seen
    change (double D v).isSome = true at yes
    change ∃ y, (ys.find? hit).bind _ = some y
    rw [seen]
    cases ev : double D v with
    | none => rw [ev] at yes; cases yes
    | some y => exact ⟨y,ev⟩

theorem regular_double {Y} (D : Term → Option Y) (reg : Regular (fun t => ∃ y, D t = some y)) :
    Regular (fun t => ∃ y, double D t = some y) := by
  obtain ⟨Q,iq,F,p,h⟩ := regular_app (regular_app regular_leaf reg) reg
  refine ⟨Q,iq,F,p,fun t => ?_⟩
  rw [h]
  constructor
  · rintro ⟨_,b,rfl,⟨_,a,rfl,rfl,ya,hya⟩,yb,hyb⟩
    exact ⟨ya,by simp [double,hyb,hya]⟩
  · rintro ⟨y,hy⟩
    cases t with
    | s => cases hy
    | app l b =>
      cases l with
      | s => cases hy
      | app f a =>
        cases f with
        | app _ _ => cases hy
        | s =>
          cases eb : D b with
          | none => simp [double,eb] at hy
          | some z =>
            exact ⟨_,b,rfl,⟨_,a,rfl,rfl,y,by simpa [double,eb] using hy⟩,z,eb⟩

/-- Any additional regular output query on the left copy is preserved, even
    on arbitrary packed inputs whose two children are unrelated. -/
theorem regular_double_query {Y} (D : Term → Option Y) (P : Y → Prop)
    (domain : Regular (fun t => ∃ y, D t = some y))
    (test : Regular (fun t => ∃ y, D t = some y ∧ P y)) :
    Regular (fun t => ∃ y, double D t = some y ∧ P y) := by
  obtain ⟨Q,iq,F,p,h⟩ := regular_app (regular_app regular_leaf test) domain
  refine ⟨Q,iq,F,p,fun t => ?_⟩
  rw [h]
  constructor
  · rintro ⟨_,b,rfl,⟨_,a,rfl,rfl,y,ha,hy⟩,z,hb⟩
    exact ⟨y,by simp [double,hb,ha],hy⟩
  · rintro ⟨y,hy,ok⟩
    cases t with
    | s => cases hy
    | app l b =>
      cases l with
      | s => cases hy
      | app f a =>
        cases f with
        | app _ _ => cases hy
        | s =>
          cases eb : D b with
          | none => simp [double,eb] at hy
          | some z =>
            exact ⟨_,b,rfl,⟨_,a,rfl,rfl,y,by simpa [double,eb] using hy,ok⟩,z,eb⟩

#print axioms first_from_parallel
#print axioms parallel_has_first
#print axioms prefix_path
end TwoScans.SerialReadout
