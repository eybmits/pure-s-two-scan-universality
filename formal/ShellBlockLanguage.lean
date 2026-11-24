import ShellLanguages
namespace TwoScans.Language
open Automata WordBlocks

private def short : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => [] :: (short n).map (false :: ·) ++ (short n).map (true :: ·)

private theorem mem_short (n : Nat) (w : List Bool) : w ∈ short n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => cases w <;> simp [short]
  | succ n ih =>
    cases w with
    | nil => simp [short]
    | cons b w => cases b <;> simp [short,ih]

abbrev Buffer (k : Nat) := {v : List Bool // v.length ≤ k}
instance (k : Nat) : FinStates (Buffer k) :=
  ⟨(short k).attachWith _ (fun w h => (mem_short k w).1 h),fun w =>
      (List.mem_attachWith _ _).2 ((mem_short k w.val).2 w.property)⟩

def decodeBlock {α} [FinStates α] (a : Alphabet α) (v : List Bool) :=
  FinStates.enum.find? (fun x => decide (v = a.code x))

theorem decodeBlock_iff {α} [FinStates α] (a : Alphabet α) (v : List Bool) (x : α) :
    decodeBlock a v = some x ↔ v = a.code x := by
  constructor
  · exact fun h => of_decide_eq_true (List.find?_some (p := fun c => decide (v = a.code c)) h)
  · intro eq
    cases e : decodeBlock a v with
    | some y =>
      have matchY : v = a.code y := of_decide_eq_true (List.find?_some (p := fun c => decide (v = a.code c)) e)
      rw [a.faithful y x (matchY.symm.trans eq)]
    | none =>
      have miss := List.find?_eq_none.mp e x (FinStates.covers x)
      exact False.elim (miss (decide_eq_true eq))

def cleanBuf (w : Nat) : Buffer w := ⟨[], by simp⟩
abbrev ChunkState (w : Nat) (Q : Type) := Option (Buffer w × Q)

def bitStep {α Q} [FinStates α] (a : Alphabet α) (step : α → Q → Q)
    (b : Bool) : ChunkState a.width Q → ChunkState a.width Q
  | none => none
  | some (buf,q) =>
    let raw := b :: buf.val
    if h : raw.length < a.width then some (⟨raw,Nat.le_of_lt h⟩,q)
    else (decodeBlock a raw).map (fun x => (cleanBuf a.width,step x q))

private theorem partial_fold {α Q} [FinStates α] (a : Alphabet α) (d : α → Q → Q)
    (v : List Bool) (q : Q) (h : v.length < a.width) :
    v.foldr (bitStep a d) (some (cleanBuf a.width,q)) = some (⟨v,Nat.le_of_lt h⟩,q) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    have lt : v.length < a.width := by simp at h; omega
    rw [List.foldr_cons,ih lt]; simp only [bitStep,dite_eq_left h]

theorem block_fold {α Q} [FinStates α] (a : Alphabet α) (d : α → Q → Q) (x : α) (q : Q) :
    (a.code x).foldr (bitStep a d) (some (cleanBuf a.width,q)) =
      some (cleanBuf a.width,d x q) := by
  have len := a.length x
  have positive := a.positive
  cases e : a.code x with
  | nil => rw [e] at len; simp at len; omega
  | cons b v =>
    rw [e] at len
    have lt : v.length < a.width := by simp at len; omega
    rw [List.foldr_cons,partial_fold a d v q lt]
    simp only [bitStep,len,Nat.lt_irrefl,dite_false]
    rw [(decodeBlock_iff a (b::v) x).2 e.symm]; rfl

theorem chunks_fold {α Q} [FinStates α] (a : Alphabet α) (d : α → Q → Q) (xs) (q : Q) :
    (chunks a xs).foldr (bitStep a d) (some (cleanBuf a.width,q)) =
     some (cleanBuf a.width,xs.foldr d q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((a.code x) ++ chunks a xs).foldr _ _ = _
    rw [List.foldr_append,ih,block_fold]; rfl

private theorem decompose_bits {α Q} [FinStates α] (a : Alphabet α) (d : α → Q → Q)
    (w : List Bool) (start : Q) {buf : Buffer a.width} {q : Q}
    (ok : w.foldr (bitStep a d) (some (cleanBuf a.width,start)) = some (buf,q)) :
    ∃ xs : List α, w = buf.val ++ chunks a xs ∧ q = xs.foldr d start := by
  induction w generalizing buf q with
  | nil => cases ok; exact ⟨[],rfl,rfl⟩
  | cons b w ih =>
    rw [List.foldr_cons] at ok
    cases e : w.foldr (bitStep a d) (some (cleanBuf a.width,start)) with
    | none => rw [e] at ok; cases ok
    | some st =>
      obtain ⟨old,y⟩ := st
      obtain ⟨xs,wx,qy⟩ := ih e
      rw [e] at ok
      simp only [bitStep] at ok
      split at ok
      · cases ok
        exact ⟨xs,congrArg (b :: ·) wx,qy⟩
      · cases z : decodeBlock a (b :: old.val) with
        | none => rw [z] at ok; cases ok
        | some c =>
          rw [z] at ok; cases ok
          have bc := (decodeBlock_iff a _ c).1 z
          exact ⟨c::xs,by change b::w = a.code c ++ chunks a xs; rw [←bc,wx]; rfl,
            by rw [List.foldr_cons,qy]⟩

theorem coded {α} [FinStates α] (a : Alphabet α) {P : List α → Prop} (hp : Reg P) :
    Reg (fun w => ∃ xs, w = chunks a xs ∧ P xs) := by
  obtain ⟨Q,iq,q,d,p,h⟩ := hp
  haveI := iq
  let accept : ChunkState a.width Q → Bool
    | none => false
    | some (buf,x) => buf.val.isEmpty && p x
  refine ⟨_,inferInstance,some (cleanBuf a.width,q),bitStep a d,accept,?_⟩
  intro w
  constructor
  · cases e : w.foldr (bitStep a d) (some (cleanBuf a.width,q)) with
    | none => intro fail; cases fail
    | some state =>
      obtain ⟨buf,z⟩ := state
      intro pass
      obtain ⟨xs,ew,ex⟩ := decompose_bits a d w q e
      change (buf.val.isEmpty && p z) = true at pass
      simp only [Bool.and_eq_true,List.isEmpty_iff] at pass
      exact ⟨xs,by simpa [pass.1] using ew,(h xs).mp (ex ▸ pass.2)⟩
  · rintro ⟨xs,rfl,px⟩
    rw [chunks_fold]; exact (h xs).mpr px

#print axioms coded
end TwoScans.Language
