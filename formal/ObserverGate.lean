import ObserverClass
import ObserverProtocol
import PayloadBits

namespace TwoScans.Observer
open Term Frames Scan Generation Live Automata TrackLayout WordBlocks PayloadBits

variable {R C : Type} [DecidableEq C]
abbrev Reading (R C : Type) := Option (Option (Label R C) × Bool)

def beginOK (slow : Bool) (v : Reading R C) := slow || (v.map Prod.snd).getD false
def endOK (slow : Bool) (v : Reading R C) :=
  slow || (match v.bind Prod.fst with | some .ve => true | _ => false)
def siteOK (current : R → C) (next : R → Option C) (slow : Bool) (r : R) (v : Reading R C) : Bool :=
  decide (readColor (v.bind Prod.fst) = (if slow then next r else some (current r)))

variable [FinStates (Label R C)]
def checks (A : Alphabet (Label R C)) (current : R → C) (next : R → Option C) (slow : Bool) :=
  tableCheck (decodeBits A) current next slow

private theorem beginAct (A : Alphabet (Label R C)) (current : R → C) (next : R → Option C) (slow : Bool)
    (v : Reading R C) : checks A current next slow true (A.code .ub) v =
    if beginOK slow v then .fast false else .stop false := by
  simp only [checks,tableCheck,decodeBits_code,beginOK]; rfl

private theorem endAct (A : Alphabet (Label R C)) (current : R → C) (next : R → Option C) (slow : Bool)
    (v : Reading R C) : checks A current next slow false (A.code .ue) v = .stop (endOK slow v) := by
  simp only [checks,tableCheck,decodeBits_code,endOK]; rfl

private theorem siteAct (A : Alphabet (Label R C)) (current : R → C) (next : R → Option C) (slow : Bool)
    (r : R) (v : Reading R C) : checks A current next slow false (A.code (.site r)) v =
    if siteOK current next slow r v then .fast false else .stop false := by
  simp only [checks,tableCheck,decodeBits_code,siteOK,decide_eq_true_eq]

def sample (s : Nat) (obs : Nat → Reading R C) (t k : Nat) := obs (t - ((k+1)*s+1))

/-- Indexed Boolean results for the finite protocol; all ages are relative to
    the start of the first block, after the header and its delimiter. -/
def GoodSamples (s : Nat) (current : R → C) (next : R → Option C) (slow : Bool)
    (us : List R) (obs : Nat → Reading R C) (t : Nat) : Prop :=
  (us.length+2)*s+1 ≤ t ∧
  beginOK slow (sample s obs t 0) = true ∧
  (∀ i (h : i < us.length), siteOK current next slow us[i] (sample s obs t (i+1)) = true) ∧
  endOK slow (sample s obs t (us.length+1)) = true

omit [DecidableEq C] [FinStates (Label R C)] in
private theorem sampleShift (s : Nat) (obs : Nat → Reading R C) (t k : Nat) :
    sample s obs (t-s) k = sample s obs t (k+1) := by
  simp only [sample,Nat.succ_mul]; congr 1; omega

private theorem tailRun (A : Alphabet (Label R C)) (g : Term) (p : List Bool)
    (classify : Term → Option (Label R C) × Bool)
    (current : R → C) (next : R → Option C) (slow : Bool) (us : List R) (t)
    (finish : Nat → Bool → Bool) :
    let obs := observedAt g classify p
    blockRun A g classify p (checks A current next slow) finish
      (us.map Label.site ++ [.ue]) t false = true ↔
    (us.length+1)*A.width+1 ≤ t ∧
    (∀ i (h : i < us.length), siteOK current next slow us[i] (sample A.width obs t i) = true) ∧
    endOK slow (sample A.width obs t us.length) = true := by
  induction us generalizing t with
  | nil =>
    dsimp only
    simp only [List.map_nil,List.nil_append,List.length_nil,Nat.zero_add,Nat.one_mul,
      blockRun,endAct,perform,sample]
    by_cases h : t < A.width + 1 <;> simp [h] <;> omega
  | cons r rs ih =>
    dsimp only
    simp only [List.map_cons,List.cons_append,blockRun,siteAct]
    have sz : (rs.length+1+1)*A.width+1 = (rs.length+1)*A.width+1 + A.width := by
      rw [Nat.succ_mul];omega
    by_cases h : t < A.width+1
    · rw [ite_eq_left h]
      have hbound : ¬ (rs.length+1+1)*A.width+1 ≤ t := by
        rw [sz]; have := A.positive; omega
      simp [hbound]
    · rw [ite_eq_right h]
      cases yes : siteOK current next slow r (observedAt g classify p (t-(A.width+1))) with
      | false =>
        simp only [Bool.false_eq_true,ite_false,perform,false_iff]
        rintro ⟨_,all,_⟩
        have v := all 0 (by simp)
        simp [sample,yes] at v
      | true =>
        simp only [ite_true,perform,ih,sampleShift,List.length_cons]
        constructor
        · rintro ⟨hn,all,done⟩
          refine ⟨by omega,?_,done⟩
          intro i hi
          cases i with
          | zero => simpa [sample] using yes
          | succ i => exact all i (by omega)
        · rintro ⟨hn,all,done⟩
          refine ⟨by omega,?_,done⟩
          intro i hi
          exact all (i+1) (by omega)

theorem blockRun_samples (A : Alphabet (Label R C)) (g : Term) (p : List Bool)
    (classify : Term → Option (Label R C) × Bool)
    (current : R → C) (next : R → Option C) (slow : Bool) (us : List R) (t)
    (finish : Nat → Bool → Bool) :
    blockRun A g classify p (checks A current next slow) finish
      (.ub :: us.map .site ++ [.ue]) t true = true ↔
    GoodSamples A.width current next slow us (observedAt g classify p) t := by
  simp only [List.cons_append,blockRun,beginAct,GoodSamples]
  have sz : (us.length+2)*A.width+1 = (us.length+1)*A.width+1 + A.width := by
    rw [show us.length+2 = (us.length+1)+1 by omega,Nat.succ_mul];omega
  by_cases h : t < A.width + 1
  · rw [ite_eq_left h]
    have hn : ¬(us.length+2)*A.width+1 ≤ t := by omega
    simp [hn]
  · rw [ite_eq_right h]
    cases yes : beginOK slow (observedAt g classify p (t - (A.width+1))) with
    | false => simp [perform,sample,yes]
    | true =>
      simp only [ite_true,perform,tailRun,sampleShift]
      simp only [sample,Nat.zero_add,Nat.one_mul,yes,true_and]
      apply and_congr_left
      intro _
      rw [sz]
      omega

/-- The actual regular tree observer at a packet checks exactly this explicit
    list of indexed observations. The same theorem applies independently for
    both fast and delayed observers, on all snapshots and all candidate words
    of the prescribed shape. -/
theorem gate_packet {tag} (ht : nf tag = true) (big : 3 ≤ size (gen tag U))
    (A : Alphabet (Label R C)) (ends : ∀ a, ∃ ds, A.code a = ds ++ [true])
    (us : List R) (vs : List C) (width : Nat) (foot : List Bool)
    (current : R → C) (next : R → Option C) (slow : Bool) (age : Nat) :
    let g := gen tag U
    let p := payload A us vs width foot
    let classify := classifier g A .vb foot
    let c := blockControl A.width slow (checks A current next slow)
    let head := 1 + (width*A.width)*(if slow then 2 else 1)
    (evaluate g classify c (rounds age (L ⋆ word g p))).1 none = true ↔
      ready p + head ≤ age ∧
      GoodSamples A.width current next slow us (observedAt g classify p) (age-ready p-head) := by
  let g := gen tag U
  let p := payload A us vs width foot
  let cl := classifier g A .vb foot
  let ck := checks A current next slow
  let c := blockControl A.width slow ck
  let head := 1 + (width*A.width)*(if slow then 2 else 1)
  let xs : List (Label R C) := .ub :: us.map .site ++ [.ue]
  let trailer := chunks A (.ve :: vs.reverse.map .color ++ [.vb]) ++ foot
  have shape : p = List.replicate (width*A.width) true ++ false::(chunks A xs ++ trailer) := by
    simp [p,payload,bodyLabels,xs,trailer,chunks,List.append_assoc]
  change (evaluate g cl c (rounds age (L ⋆ word g p))).1 none = true ↔
    ready p + head ≤ age ∧ GoodSamples A.width current next slow us (observedAt g cl p) (age-ready p-head)
  rw [controller_packet ht big]
  by_cases early : age < ready p
  · rw [ite_eq_left early]; simp; omega
  rw [ite_eq_right early]
  have hx := header_exact g cl p A.width slow ck (width*A.width) (chunks A xs ++ trailer) (age-ready p)
  rw [←shape] at hx
  change wordControl g cl c p p (age-ready p) none = _ at hx
  rw [hx]
  change (if age-ready p < head then false else _) = true ↔ _
  by_cases short : age-ready p < head
  · rw [ite_eq_left short]; simp; omega
  rw [ite_eq_right short,blocks_exact A ends,blockRun_samples]
  exact ⟨fun h => ⟨by omega,h⟩,And.right⟩

#print axioms gate_packet
end TwoScans.Observer
