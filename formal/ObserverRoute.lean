import ObserverScan

namespace TwoScans.Observer
open Term Frames Scan Generation Live

private theorem rounds_succ_last (k : Nat) (t : Term) :
    rounds (k+1) t = pi (rounds k t) := by
  rw [Frames.rounds_add]; rfl

private theorem childRounds {l r} (live : PiLive l ∨ PiLive r) (j) :
    rounds j (l ⋆ r) = rounds j l ⋆ rounds j r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [rounds_succ_last,ih]
    rcases live with hl | hr
    · simp [pi,hl j]
    · simp [pi,hr j]

private theorem leftLive {l r} (h : PiLive l ∨ PiLive r) : PiLive (l ⋆ r) := by
  intro j
  rw [childRounds h]
  rcases h with hl | hr
  · simp [nf,hl j]
  · simp [nf,hr j]

private theorem advanceLive {t} (h : PiLive t) (n) : PiLive (rounds n t) :=
  fun j => by rw [← Frames.rounds_add]; exact h _

inductive Slot where
  | a (next : Term)
  | b (fast slow scan : Term)
  deriving DecidableEq

/-- One actual syntax-directed test. A B is visible only after its second split. -/
def slot (g : Term) : Term → Option Slot
  | .s => none
  | .app left right =>
    if nf right then none
    else if nf left then
      match left with
      | .app q v => if isUnaryWord g q && isV g v then some (.a right) else none
      | _ => none
    else
      match right with
      | .app scanner cont => if nf cont then none else some (.b left cont scanner)
      | _ => none

private theorem slot_a (g q v r) (hq : isUnaryWord g q = true)
    (hv : isV g v = true) (hn : nf (q ⋆ v) = true) (hr : nf r = false) :
    slot g ((q ⋆ v) ⋆ r) = some (.a r) := by simp [slot,hq,hv,hn,hr]

private theorem slot_b (g fast scanner cont) (hf : nf fast = false) (hc : nf cont = false) :
    slot g (fast ⋆ (scanner ⋆ cont)) = some (.b fast cont scanner) := by simp [slot,nf,hf,hc]

def branch (g : Term) (payload w : List Bool) :=
  folded g (word g payload) w ⋆ probeV g payload

def scanner (g : Term) (payload : List Bool) := word g payload ⋆ probeV g payload

theorem probe_normal {g} (hg : nf g = true) (p) : nf (probeV g p) = true := by
  simp [probeV,operand,nf,root,word_normal hg]

private theorem branch_live {g} (hg : nf g = true) (p) (base : Growing (g ⋆ probeV g p)) (w) :
    PiLive (branch g p w) :=
  (Growing.ofVisible (descend hg (word_normal hg p) (probe_normal hg p) w) base).piLive

theorem slot_initial {g} (hg : nf g = true) (p w) : slot g (branch g p w) = none := by
  simp [branch,slot,probe_normal hg]

theorem slot_terminal {g} (hg : nf g = true) (p j)
    (base : Growing (g ⋆ probeV g p)) :
    slot g (rounds j (branch g p [])) = none := by
  cases j with
  | zero => exact slot_initial hg _ _
  | succ j =>
    let v := probeV g p
    let q := s ⋆ word g p
    have hq : nf (q ⋆ v) = true := by simp [q,v,nf,root,word_normal hg,probe_normal hg]
    have hv := probe_normal hg p
    change slot g (rounds j (pi ((s ⋆ g ⋆ q) ⋆ v))) = none
    have run : pi ((s ⋆ g ⋆ q) ⋆ v) = (g ⋆ v) ⋆ (q ⋆ v) := by
      simp [pi,nf,root,q,v,hg,word_normal hg,hv]
    rw [run,childRounds (.inl base.piLive),Frames.rounds_fixed hq]
    simp [slot,hq]

theorem slot_firstA {g} (hg : nf g = true) (p w j)
    (base : Growing (g ⋆ probeV g p)) :
    slot g (rounds (j+1) (branch g p (false::w))) = some (.a (rounds j (branch g p w))) := by
  let v := probeV g p
  let q := s ⋆ word g p
  have hq : nf (q ⋆ v) = true := by simp [q,v,nf,root,word_normal hg,probe_normal hg]
  have live := branch_live hg p base w
  change slot g (rounds j (pi ((s ⋆ q ⋆ folded g (word g p) w) ⋆ v))) = _
  rw [A_extract (word_normal hg _) (folded_normal hg (word_normal hg p) _) (probe_normal hg _)]
  change slot g (rounds j ((q ⋆ v) ⋆ branch g p w)) = _
  rw [childRounds (.inr live),Frames.rounds_fixed hq]
  apply slot_a
  · exact (unaryWord_spec _ _).2 ⟨p,rfl⟩
  · exact (isV_spec _ _).2 ⟨p,p,rfl⟩
  · exact hq
  · exact live _

theorem slot_firstB {g} (hg : nf g = true) (p w) :
    slot g (rounds 1 (branch g p (true::w))) = none := by
  let v := probeV g p
  let r := folded g (word g p) w
  have hv := probe_normal hg p
  change slot g (pi ((s ⋆ r ⋆ ((s ⋆ word g p) ⋆ r)) ⋆ v)) = none
  rw [B_direct (word_normal hg _) (folded_normal hg (word_normal hg p) _) hv]
  have red := folded_applied_red g (word g p) v w
  change nf (r ⋆ v) = false at red
  change slot g ((r ⋆ v) ⋆ (((s ⋆ word g p) ⋆ r) ⋆ v)) = none
  have hn : nf (((s ⋆ word g p) ⋆ r) ⋆ v) = false := by simp [nf,root]
  change nf v = true at hv
  simp [slot,hn,red,hv]

theorem slot_splitB {g} (hg : nf g = true) (p w j)
    (base : Growing (g ⋆ probeV g p)) :
    slot g (rounds (j+2) (branch g p (true::w))) =
    some (.b (rounds (j+1) (branch g p w)) (rounds j (branch g p w))
          (rounds j (scanner g p))) := by
  let v := probeV g p
  let r := folded g (word g p) w
  have hv := probe_normal hg p
  have live := branch_live hg p base w
  have live1 := advanceLive live 1
  rw [Nat.add_comm j 2,Frames.rounds_add]
  change slot g (rounds j (rounds 2 ((s ⋆ r ⋆ ((s ⋆ word g p) ⋆ r)) ⋆ v))) = _
  rw [B_delayed (word_normal hg _) (folded_normal hg (word_normal hg p) _) hv]
  change slot g (rounds j ((rounds 1 (branch g p w)) ⋆ (scanner g p ⋆ branch g p w))) = _
  rw [childRounds (.inl live1),childRounds (.inr live)]
  apply slot_b
  · exact live1 j
  · exact live j

/-- Follow one specified finite route, rejecting any wrongly guessed A or B. -/
def seek (g : Term) : List Choice → Term → Option Term
  | [], t => match slot g t with | some (.b _ _ scan) => some scan | _ => none
  | c :: path, t =>
    match c,slot g t with
    | .a,some (.a next) => seek g path next
    | .bFast,some (.b fast _ _) => seek g path fast
    | .bSlow,some (.b _ slow _) => seek g path slow
    | _,_ => none

/-- Independent word-level specification; fails exactly at a mismatched
    prefix or an unavailable split. Each successful result is the scanner age. -/
def ageAt : List Choice → List Bool → Nat → Option Nat
  | [], true::_, j+2 => some j
  | .a::cs,false::w,j+1 => ageAt cs w j
  | .bFast::cs,true::w,j+2 => ageAt cs w (j+1)
  | .bSlow::cs,true::w,j+2 => ageAt cs w j
  | _,_,_ => none

theorem seek_exact {g} (hg : nf g = true) (p) (base : Growing (g ⋆ probeV g p))
    (path : List Choice) (w j) :
    seek g path (rounds j (branch g p w)) =
      (ageAt path w j).map (fun age => rounds age (scanner g p)) := by
  induction path generalizing w j with
  | nil =>
    cases w with
    | nil => simp [seek,ageAt,slot_terminal hg p j base]
    | cons b w =>
      cases j with
      | zero => cases b <;> simp [seek,ageAt,rounds,slot_initial hg]
      | succ j =>
        cases b with
        | false => simp [seek,ageAt,slot_firstA hg p w j base]
        | true =>
          cases j with
          | zero => simp [seek,ageAt,slot_firstB hg]
          | succ j => simp [seek,ageAt,slot_splitB hg p w j base]
  | cons c cs ih =>
    cases w with
    | nil => cases c <;> simp [seek,ageAt,slot_terminal hg p j base]
    | cons b w =>
      cases j with
      | zero => cases c <;> cases b <;> simp [seek,ageAt,rounds,slot_initial hg]
      | succ j =>
        cases b with
        | false => cases c <;> simp [seek,ageAt,slot_firstA hg p w j base,ih]
        | true =>
          cases j with
          | zero => cases c <;> simp [seek,ageAt,slot_firstB hg]
          | succ j => cases c <;> simp [seek,ageAt,slot_splitB hg p w j base,ih]

theorem probe_observation {tag} (ht : nf tag = true)
    (big : 3 ≤ size (gen tag U)) (p path w j) :
    let g := gen tag U
    ((seek g path (rounds j (branch g p w))).bind (read g)) =
      (ageAt path w j).bind (fun a =>
        if a < p.length then some (word g (p.drop a)) else none) := by
  let g := gen tag U
  have hg : nf g = true := gen_normal ht (by decide)
  have base := genGrowth ht (probe_normal hg p)
  change ((seek g path (rounds j (branch g p w))).bind (read g)) = _
  rw [seek_exact hg p base]
  cases h : ageAt path w j with
  | none => rfl
  | some a => exact read_exact hg big p a

#print axioms probe_observation
end TwoScans.Observer
