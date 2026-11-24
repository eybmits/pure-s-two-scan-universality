import ObserverControl
import TrackLayout

namespace TwoScans.Observer
open Term Frames Automata TrackLayout

/-- All binary words of length at most n, with their proofs attached. -/
def shortTable : (n : Nat) → List {w : List Bool // w.length ≤ n}
  | 0 => [⟨[],by simp⟩]
  | n+1 =>
    ⟨[],by simp⟩ :: [false,true].flatMap (fun b =>
      (shortTable n).map (fun w => ⟨b :: w.1,by simp; omega⟩))

theorem shortTable_covers (n) (x : {w : List Bool // w.length ≤ n}) : x ∈ shortTable n := by
  induction n with
  | zero =>
    obtain ⟨_ | ⟨b,w⟩,h⟩ := x
    · simp [shortTable]
    · simp at h
  | succ n ih =>
    obtain ⟨_ | ⟨b,w⟩,h⟩ := x
    · simp [shortTable]
    · simp only [shortTable,List.mem_cons,List.mem_flatMap,List.mem_map]
      right
      refine ⟨b,by cases b <;> simp,⟨w,by simp at h; omega⟩,ih _,?_⟩
      rfl

abbrev Short (n : Nat) := {w : List Bool // w.length ≤ n}
instance (n : Nat) : FinStates (Short n) := ⟨shortTable n,shortTable_covers n⟩
abbrev BlockState (s : Nat) := Option (Bool × Short s)

def blank (n : Nat) : Short n := ⟨[],by simp⟩
def checking (s) (first : Bool) : BlockState s := some (first,blank s)

def afterBlock {s} (a : Action Bool) : Action (BlockState s) :=
  match a with
  | .stop b => .stop b
  | .fast q | .slow q => .fast (checking s q)

/-- In block mode both routes always descend the fast way. Decisions at the
    last bit can inspect its scanner; an A at that position rejects. -/
def ingest {X} (s : Nat) (check : Bool → List Bool → Option X → Action Bool)
    (first : Bool) (pre : Short s) (bit : Bool) (observed : Option X) : Action (BlockState s) :=
  let xs := pre.1 ++ [bit]
  if h : xs.length < s then .fast (some (first,⟨xs,by omega⟩))
  else if bit then afterBlock (check first xs observed) else .stop false

def blockControl {X} (s : Nat) (delayed : Bool) (check : Bool → List Bool → Option X → Action Bool) :
    Control (BlockState s) X where
  onA
    | none => .fast (checking s true)
    | some (f,pre) => ingest s check f pre false none
  onB q seen :=
    match q with
    | none => if delayed then .slow none else .fast none
    | some (f,pre) => ingest s check f pre true seen

/-- Fixed checks at the matched final B of each block. UB calibrates the fast
    route against the exact terminal suffix; UE checks its VE mirror. -/
def tableCheck {R C : Type} [DecidableEq C]
    (decode : List Bool → Option (Label R C)) (current : R → C) (next : R → Option C)
    (slow first : Bool) (block : List Bool) (seen : Option (Option (Label R C) × Bool)) : Action Bool :=
  let tag := seen.bind (fun a => a.1)
  match first, decode block with
  | true,some .ub => if slow || (seen.map Prod.snd).getD false then .fast false else .stop false
  | false,some .ue => .stop (slow || (match tag with | some .ve => true | _ => false))
  | false,some (.site r) =>
    let target := if slow then next r else some (current r)
    if readColor tag = target then .fast false else .stop false
  | _,_ => .stop false

/-- Number of local rounds before a final-bit read in a fast block. -/
def blockAge (t n : Nat) := t - n - 1

def observedAt {X} (g : Term) (classify : Term → X) (p : List Bool) (age : Nat) :=
  if age < p.length then some (classify (word g (p.drop age))) else none

theorem prefixStep {X} (g : Term) (classify : Term → X) (p : List Bool)
    (s : Nat) (slow : Bool) (check : Bool → List Bool → Option X → Action Bool)
    (f : Bool) (pre : Short s) (b : Bool) (w : List Bool) (t : Nat)
    (short : (pre.1 ++ [b]).length < s) :
    wordControl g classify (blockControl s slow check) p (b::w) (t+2) (some (f,pre)) =
    wordControl g classify (blockControl s slow check) p w (t+1)
      (some (f,⟨pre.1 ++ [b],by omega⟩)) := by
  have hh : pre.1.length+1 < s := by simpa using short
  cases b <;> simp [wordControl,blockControl,ingest,hh,perform]

private theorem finalStep {X} (g : Term) (classify : Term → X) (p : List Bool)
    (s : Nat) (slow : Bool) (check : Bool → List Bool → Option X → Action Bool)
    (f : Bool) (pre : Short s) (w : List Bool) (t : Nat)
    (full : (pre.1 ++ [true]).length = s) :
    let rest := fun q => wordControl g classify (blockControl s slow check) p w (t+1) (checking s q)
    wordControl g classify (blockControl s slow check) p (true::w) (t+2) (some (f,pre)) =
      perform (check f (pre.1 ++ [true]) (observedAt g classify p t)) rest rest := by
  have h : ¬ (pre.val ++ [true]).length < s := by omega
  simp only [wordControl,blockControl,ingest,h,dite_false,ite_true,observedAt]
  cases check f (pre.val ++ [true]) _ <;> rfl

/-- One entire fixed-width block, ending in B, is read by the actual finite
    controller. It consumes exactly its width in rounds and consults the
    scanner only at the indicated final-bit age. -/
theorem blockStep {X} (g : Term) (classify : Term → X) (p : List Bool)
    (s) (slow : Bool) (check : Bool → List Bool → Option X → Action Bool)
    (f : Bool) (pre : Short s) (digits w : List Bool) (age : Nat)
    (full : pre.1.length + digits.length + 1 = s) :
    let rest := fun q => wordControl g classify (blockControl s slow check) p w (age+1) (checking s q)
    wordControl g classify (blockControl s slow check) p (digits ++ true::w) (age+2+digits.length) (some (f,pre)) =
      perform (check f (pre.1 ++ digits ++ [true]) (observedAt g classify p age)) rest rest := by
  induction digits generalizing pre with
  | nil => simpa using finalStep g classify p s slow check f pre w age (by simpa using full)
  | cons b ds ih =>
    have hs : (pre.1 ++ [b]).length < s := by simp_all; omega
    let n : Short s := ⟨pre.1 ++ [b],by omega⟩
    have hnext : n.val.length + ds.length + 1 = s := by
      calc
        _ = pre.val.length+(b::ds).length+1 := by simp [n]; omega
        _ = s := full
    have h := prefixStep g classify p s slow check f pre b (ds ++ true::w) (age+ds.length+1) hs
    simp only [List.cons_append]
    rw [show age+2+(b::ds).length = age+ds.length+1+2 by simp; omega,h]
    rw [show age+ds.length+1+1 = age+2+ds.length by omega]
    simpa [n,List.append_assoc] using ih n hnext

/-- The run of header B's determines the relative offset of the two routes.
    Both subsequently cross the delimiter A and reset the same block parser. -/
theorem headerStep {X} (g : Term) (classify : Term → X) (p : List Bool)
    (s) (slow : Bool) (check : Bool → List Bool → Option X → Action Bool)
    (n : Nat) (w : List Bool) (age : Nat) :
    wordControl g classify (blockControl s slow check) p (List.replicate n true ++ false::w)
        (age + 1 + n * (if slow then 2 else 1)) none =
    wordControl g classify (blockControl s slow check) p w age (checking s true) := by
  induction n with
  | zero => cases slow <;> rfl
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append]
    cases slow with
    | false =>
      simp only [Bool.false_eq_true,ite_false,Nat.mul_one] at *
      rw [show age+1+(n+1) = (age+n)+2 by omega]
      simpa [wordControl,blockControl,perform,show age+n+1 = age+1+n by omega] using ih
    | true =>
      simp only [ite_true,Nat.add_mul,Nat.one_mul] at *
      rw [show age+1+(n*2+2) = (age+1+n*2)+2 by omega]
      simpa [wordControl,blockControl,perform] using ih

#print axioms blockStep
#print axioms headerStep
end TwoScans.Observer
