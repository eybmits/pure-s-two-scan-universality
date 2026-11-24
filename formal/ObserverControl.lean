import ObserverFinite
import ShellWordAutomata

namespace TwoScans.Observer
open Term Frames Scan Generation Live Automata

theorem route_regular {Q X : Type} [FinStates Q] [DecidableEq Q] [FinStates X]
    (g) (classify : Term → X) (hc : Attribute classify) (c : Control Q X) (q : Q) :
    Regular (fun t => (evaluate g classify c t).1 q = true) := by
  obtain ⟨R,ir,a,out,h⟩ := routeAttribute g classify hc c
  exact ⟨R,ir,a,fun x => (out x).1 q,fun t => by dsimp only; rw [h]⟩

theorem boolAttribute {b : Term → Bool} (h : Regular (fun t => b t = true)) : Attribute b := by
  obtain ⟨Q,iq,a,out,ok⟩ := h
  exact ⟨Q,iq,a,out,fun t => Bool.eq_iff_iff.mpr (ok t)⟩

theorem pairAttribute {X Y : Type} {f : Term → X} {g : Term → Y} (hf : Attribute f) (hg : Attribute g) :
    Attribute (fun t => (f t,g t)) := attrPair hf hg

theorem mapAttribute {X Y : Type} {f : Term → X} (hf : Attribute f) (g : X → Y) :
    Attribute (fun t => g (f t)) := attrMap hf g

private theorem no_slot {Q X} {g t} (classify : Term → X) (c : Control Q X) (q : Q)
    (h : slot g t = none) : (evaluate g classify c t).1 q = false := by
  cases t with
  | s => rfl
  | app l r => simp [evaluate,h]

private theorem a_slot {Q X} {g t next} (classify : Term → X) (c : Control Q X) (q : Q)
    (h : slot g t = some (.a next)) :
    (evaluate g classify c t).1 q =
      perform (c.onA q) (evaluate g classify c next).1 (evaluate g classify c next).1 := by
  cases t with
  | s => cases h
  | app l r =>
    simp only [evaluate,h]
    have eq : r = next := by
      cases l <;> cases r <;> simp only [slot] at h
      all_goals repeat' split at h
      all_goals simp_all
    rw [eq]

private theorem b_slot {Q X} {g t fast slow scan} (classify : Term → X) (c : Control Q X) (q : Q)
    (h : slot g t = some (.b fast slow scan)) :
    (evaluate g classify c t).1 q =
      perform (c.onB q ((read g scan).map classify))
        (evaluate g classify c fast).1 (evaluate g classify c slow).1 := by
  cases t with
  | s => cases h
  | app l r =>
    simp only [evaluate,h]
    have eq : l = fast ∧ r = scan ⋆ slow := by
      cases l <;> cases r <;> simp only [slot] at h
      all_goals repeat' split at h
      all_goals simp_all
    rw [eq.1,eq.2]
    rfl

/-- Whole control program evaluated on a mathematical word/clock. Every B gets
    the label at the current local scanner age. Both reductions in time count
    actual S rounds; the recursion on the word simply specifies the answer. -/
def wordControl {Q X} (g : Term) (classify : Term → X) (c : Control Q X) (p : List Bool) :
    List Bool → Nat → Q → Bool
  | false :: w, t+1, q => perform (c.onA q)
      (wordControl g classify c p w t) (wordControl g classify c p w t)
  | true :: w, t+2, q => perform
      (c.onB q (if t < p.length then some (classify (word g (p.drop t))) else none))
      (wordControl g classify c p w (t+1)) (wordControl g classify c p w t)
  | _, _, _ => false

theorem controller_branch {Q X} {tag} (ht : nf tag = true) (big : 3 ≤ size (gen tag U))
    (classify : Term → X) (c : Control Q X) (p w j q) :
    let g := gen tag U
    (evaluate g classify c (rounds j (branch g p w))).1 q = wordControl g classify c p w j q := by
  let g := gen tag U
  have hg : nf g = true := gen_normal ht (by decide)
  have base := genGrowth ht (probe_normal hg p)
  change (evaluate g classify c _).1 q = wordControl g classify c p w j q
  induction w generalizing j q with
  | nil =>
    rw [no_slot classify c q (slot_terminal hg p j base)]
    rfl
  | cons b w ih =>
    cases j with
    | zero =>
      change (evaluate g classify c (branch g p (b::w))).1 q = _
      rw [no_slot classify c q (slot_initial hg p (b::w))]
      cases b <;> rfl
    | succ j =>
      cases b with
      | false =>
        rw [a_slot classify c q (slot_firstA hg p w j base)]
        have eq : (evaluate g classify c (rounds j (branch g p w))).1 = _ := funext (ih j)
        simp only [wordControl,eq]
      | true =>
        cases j with
        | zero => rw [no_slot classify c q (slot_firstB hg p w)]; rfl
        | succ j =>
          rw [b_slot classify c q (slot_splitB hg p w j base)]
          have eqf : (evaluate g classify c (rounds (j+1) (branch g p w))).1 = _ := funext (ih (j+1))
          have eqs : (evaluate g classify c (rounds j (branch g p w))).1 = _ := funext (ih j)
          have rd := read_exact hg big p j
          change read g (rounds j (scanner g p)) = _ at rd
          simp only [wordControl,eqf,eqs,rd]
          split <;> rfl

/-- An entire syntax-directed controller, deterministic including its direction
    choices, on the original L packet, equals its word-and-age specification. -/
theorem controller_packet {Q X} {tag} (ht : nf tag = true) (big : 3 ≤ size (gen tag U))
    (classify : Term → X) (c : Control Q X) (p t q) :
    let g := gen tag U
    (evaluate g classify c (rounds t (L ⋆ word g p))).1 q =
      if t < ready p then false else wordControl g classify c p p (t-ready p) q := by
  let g := gen tag U
  have hg : nf g = true := gen_normal ht (by decide)
  change (evaluate g classify c _).1 _ = _
  split
  next h => apply no_slot; exact slot_before hg p t h
  next h =>
    have parts : ready p + (t-ready p) = t := by omega
    have eq : rounds t (L ⋆ word g p) = rounds (t-ready p) (branch g p p) := by
      calc
        _ = rounds (ready p + (t-ready p)) (L ⋆ word g p) := congrArg (fun n => rounds n _) parts.symm
        _ = _ := by rw [Frames.rounds_add,becomeBranch hg]
    rw [eq]
    exact controller_branch ht big classify c p p _ q

#print axioms route_regular
#print axioms controller_packet
end TwoScans.Observer
