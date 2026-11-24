import TableauSites

namespace TwoScans.Tableau.OneTape
variable {Q Γ : Type}

inductive Dir | left | stay | right deriving DecidableEq, Repr
structure Instruction (Q Γ : Type) where
  state : Q
  write : Γ
  move : Dir
deriving DecidableEq, Repr
abbrev Table (Q Γ : Type) := Q → Γ → Instruction Q Γ
inductive Color (Q Γ : Type)
  | plain : Γ → Color Q Γ
  | head : Q → Γ → Color Q Γ
  | wall : Color Q Γ
deriving DecidableEq, Repr
open Color

def enters (δ : Table Q Γ) (d : Dir) : Option (Color Q Γ) → Option Q
  | some (.head q a) => if (δ q a).move = d then some (δ q a).state else none
  | _ => none

@[local simp] private theorem enter_none (δ : Table Q Γ) (d : Dir) : enters δ d none = none := rfl
@[local simp] private theorem enter_plain (δ : Table Q Γ) (d : Dir) (a : Γ) : enters δ d (some (plain a)) = none := rfl
@[local simp] private theorem enter_wall (δ : Table Q Γ) (d : Dir) : enters δ d (some wall) = none := rfl
@[local simp] private theorem enter_head (δ : Table Q Γ) (d : Dir) (q : Q) (a : Γ) : enters δ d (some (head q a)) = (if (δ q a).move = d then some (δ q a).state else none) := rfl

def rule (δ : Table Q Γ) : Rule (Color Q Γ) := fun l c r =>
  match c with
  | .wall => .wall
  | .head q a =>
    let z := δ q a
    match z.move with
    | .stay => .head z.state z.write
    | .left => if l.isNone then .head z.state z.write else .plain z.write
    | .right => .plain z.write
  | .plain a =>
    match (enters δ .right l).or (enters δ .left r) with
    | none => .plain a
    | some q => .head q a

/-- A finite-tape zipper. Off the left end a move stays put; crossing the
right wall is a failed bounded run. A successful source trace never crosses. -/
structure Cfg (Q Γ : Type) where
  left : List Γ   -- nearest cell first
  state : Q
  here : Γ
  right : List Γ  -- nearest cell first
deriving DecidableEq, Repr

def encode (c : Cfg Q Γ) : List (Color Q Γ) :=
  c.left.reverse.map .plain ++ (.head c.state c.here :: (c.right.map .plain ++ [.wall]))

def dead (a : List Γ) : List (Color Q Γ) := a.map .plain ++ [.wall]

def bounded (δ : Table Q Γ) (c : Cfg Q Γ) : Option (Cfg Q Γ) :=
  let z := δ c.state c.here
  match z.move with
  | .stay => some ⟨c.left, z.state, z.write, c.right⟩
  | .left =>
    match c.left with
    | [] => some ⟨[], z.state, z.write, c.right⟩
    | a :: as => some ⟨as, z.state, a, z.write :: c.right⟩
  | .right =>
    match c.right with
    | [] => none
    | a :: as => some ⟨z.write :: c.left, z.state, a, as⟩

private theorem quietHead (δ : Table Q Γ) (r : List Γ) :
    enters δ .left ((r.map plain ++ [wall]).head?) = none := by
  cases r <;> rfl

private theorem quiet_suffix (δ : Table Q Γ) (p : Option (Color Q Γ)) (r : List Γ)
    (hp : enters δ .right p = none) :
    sweep (rule δ) p (r.map plain ++ [wall]) = r.map plain ++ [wall] := by
  induction r generalizing p with
  | nil => rfl
  | cons a as ih =>
    simp [sweep, rule, hp, -List.head?_append, quietHead, ih (some (plain a)) rfl]

private theorem quiet_prefix (δ : Table Q Γ) (p : Option (Color Q Γ))
    (hp : enters δ .right p = none) (pre : List Γ) (a : Γ) (tail : List (Color Q Γ)) :
    sweep (rule δ) p (pre.map plain ++ (plain a :: tail)) =
      pre.map plain ++ sweep (rule δ) none (plain a :: tail) := by
  induction pre generalizing p with
  | nil => simp [sweep, rule, hp]
  | cons b bs ih =>
    have h := ih (some (plain b)) rfl
    cases bs <;> simp_all [sweep, rule, -List.head?_append, -List.map_reverse]

/-- Every legal machine step is one radius-one sweep on the encoded zipper. -/
theorem sweep_of_step (δ : Table Q Γ) (c c' : Cfg Q Γ)
    (h : bounded δ c = some c') :
    sweep (rule δ) none (encode c) = encode c' := by
  rcases c with ⟨l,q,a,r⟩
  generalize hz : δ q a = z at *
  rcases z with ⟨q',b,d⟩
  cases l with
  | nil =>
    cases r with
    | nil => cases d <;> simp_all [bounded, encode, sweep, rule, -List.head?_append, -List.map_reverse] <;> subst c' <;> rfl
    | cons u us =>
      cases d <;> simp_all [bounded] <;> subst c'
      all_goals simp [encode, sweep, rule, -List.head?_append, -List.map_reverse, hz, quietHead, quiet_suffix δ (some (plain u)) us rfl]
  | cons x xs =>
    cases r with
    | nil =>
      cases d <;> simp_all [bounded] <;> subst c'
      all_goals simp [encode, List.append_assoc, quiet_prefix δ none rfl, sweep, rule, -List.head?_append, -List.map_reverse, hz]
    | cons u us =>
      cases d <;> simp_all [bounded] <;> subst c'
      all_goals simp [encode, List.append_assoc, quiet_prefix δ none rfl, sweep, rule, -List.head?_append, -List.map_reverse,
        hz, quietHead, quiet_suffix δ (some (plain u)) us rfl]

/-- If a source step misses the right wall, the rule simulation loses its
only head. This cannot produce a later spurious successful configuration. -/
theorem sweep_of_escape (δ : Table Q Γ) (c : Cfg Q Γ) (h : bounded δ c = none) :
    ∃ cells, sweep (rule δ) none (encode c) = dead cells := by
  rcases c with ⟨l,q,a,r⟩
  generalize hz : δ q a = z at *
  rcases z with ⟨q',b,d⟩
  cases d <;> cases r <;> cases l <;> simp_all [bounded]
  case right.nil.nil => exact ⟨[b], by simp [encode, dead, sweep, rule, hz]⟩
  case right.nil.cons x xs =>
    exact ⟨xs.reverse ++ [x,b], by
      simp [dead, encode, List.append_assoc, quiet_prefix δ none rfl, sweep, rule, -List.head?_append, -List.map_reverse, hz]⟩

theorem dead_fixed (δ : Table Q Γ) (cells : List Γ) :
    sweep (rule δ) none (dead cells) = dead cells :=
  quiet_suffix δ none cells rfl

#print axioms sweep_of_step
#print axioms sweep_of_escape
#print axioms dead_fixed
end TwoScans.Tableau.OneTape
