import Anchors

namespace TwoScans.Frames
open Term
infixl:65 " ⋆ " => Term.app

def root : Term → Term → Option Term
  | .app (.app .s x) y, z => some ((x ⋆ z) ⋆ (y ⋆ z))
  | _, _ => none

def nf : Term → Bool
  | .s => true
  | .app a b => (root a b).isNone && nf a && nf b

def pi : Term → Term
  | .s => .s
  | .app a b =>
    if nf a && nf b then (root a b).getD (a ⋆ b)
    else pi a ⋆ pi b

theorem root_sound {a b u} (h : root a b = some u) : Step (a ⋆ b) u := by
  unfold root at h
  split at h
  · cases h
    exact .root _ _ _
  · cases h

theorem nf_iff_normal (t : Term) : nf t = true ↔ Normal t := by
  induction t with
  | s =>
    constructor
    · intro _ _ st
      cases st
    · intro _
      rfl
  | app a b ha hb =>
    simp only [nf, Bool.and_eq_true, Option.isNone_iff_eq_none, ha, hb]
    constructor
    · rintro ⟨⟨nr, na⟩, nb⟩ u st
      cases st with
      | root x y z => simp [root] at nr
      | left r st => exact na _ st
      | right l st => exact nb _ st
    · intro h
      have nr : root a b = none := by
        cases e : root a b with
        | none => rfl
        | some u => exact (h _ (root_sound e)).elim
      exact ⟨⟨nr, fun u st => h _ (.left b st)⟩, fun u st => h _ (.right a st)⟩

theorem fixed {t : Term} (hn : nf t = true) : pi t = t := by
  cases t with
  | s => rfl
  | app a b =>
    simp only [nf, Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
    obtain ⟨⟨nr, na⟩, nb⟩ := hn
    simp [pi, na, nb, nr]

/-- A counted sequence of maximal parallel innermost rounds in which each
    starting term is nonnormal. The final term may itself be reducible. -/
inductive Strict : Nat → Term → Term → Prop where
  | zero (t) : Strict 0 t t
  | next {n t u} : nf t = false → Strict n (pi t) u → Strict (n+1) t u

def rounds : Nat → Term → Term
  | 0, t => t
  | n+1, t => rounds n (pi t)

theorem Strict.result {n t u} (h : Strict n t u) : rounds n t = u := by
  induction h with
  | zero => rfl
  | next _ _ ih => exact ih

theorem Strict.before {n t u} (h : Strict n t u) :
    ∀ k < n, nf (rounds k t) = false := by
  induction h with
  | zero => intro k hk; omega
  | next hn _ ih =>
    intro k hk
    cases k with
    | zero => exact hn
    | succ k => exact ih k (by omega)

theorem Strict.append {n m t u v} (h : Strict n t u) (h' : Strict m u v) :
    Strict (n+m) t v := by
  induction h with
  | zero => simpa using h'
  | next hn _ ih =>
    rw [Nat.succ_add]
    exact .next hn (ih h')

theorem Strict.under {n t u f} (h : Strict n t u) (hf : nf f = true) :
    Strict n (f ⋆ t) (f ⋆ u) := by
  induction h with
  | zero => exact .zero _
  | next hn _ ih =>
    apply Strict.next
    · simp [nf, hn]
    · simpa [pi, hn, fixed hf] using ih

def A := s ⋆ s
def B := s ⋆ A

/-- true represents B, false represents A. -/
def word (g : Term) : List Bool → Term
  | [] => s ⋆ g
  | false :: rest => A ⋆ word g rest
  | true :: rest => B ⋆ word g rest

def cost : List Bool → Nat
  | [] => 0
  | false :: rest => cost rest + 1
  | true :: rest => cost rest + 2

/-- Normal form for the special tester q=S p. -/
def folded (g p : Term) : List Bool → Term
  | [] => s ⋆ g ⋆ (s ⋆ p)
  | false :: rest => s ⋆ (s ⋆ p) ⋆ folded g p rest
  | true :: rest => s ⋆ folded g p rest ⋆ ((s ⋆ p) ⋆ folded g p rest)

theorem word_normal {g} (hg : nf g = true) (w) : nf (word g w) = true := by
  induction w with
  | nil => simp [word,nf,root,hg]
  | cons v w ih => cases v <;> simp [word,A,B,nf,root,ih]

theorem folded_normal {g p} (hg : nf g = true) (hp : nf p = true) (w) :
    nf (folded g p w) = true := by
  induction w with
  | nil => simp [folded,nf,root,hg,hp]
  | cons v w ih => cases v <;> simp [folded,nf,root,hp,ih]

/-- Exact native preparation time and raw resulting tree for every word. -/
theorem prepare {g p} (hg : nf g = true) (hp : nf p = true) (w : List Bool) :
    Strict (cost w) (word g w ⋆ (s ⋆ p)) (folded g p w) := by
  induction w with
  | nil => exact .zero _
  | cons v w ih =>
    have hw := word_normal hg w
    have hr := folded_normal hg hp w
    cases v with
    | false =>
      apply Strict.next
      · simp [word,A,nf,root]
      · have h := ih.under (f := s ⋆ (s ⋆ p)) (by simp [nf,root,hp])
        simpa [word,folded,pi,A,nf,root,hp,hw] using h
    | true =>
      apply Strict.next
      · simp [word,B,A,nf,root]
      · have h := ih.under (f := A ⋆ (s ⋆ p)) (by simp [nf,root,A,hp])
        have last : Strict 1 ((A ⋆ (s ⋆ p)) ⋆ folded g p w)
              (folded g p (true::w)) := by
          apply Strict.next
          · simp [A,nf,root]
          · simpa [A,folded,pi,nf,root,hp,hr] using Strict.zero (folded g p (true::w))
        simpa [word,B,A,pi,nf,root,hp,hw] using h.append last

theorem A_extract {p r v} (hp : nf p = true) (hr : nf r = true)
    (hv : nf v = true) :
    pi ((s ⋆ (s ⋆ p) ⋆ r) ⋆ v) = ((s ⋆ p) ⋆ v) ⋆ (r ⋆ v) := by
  simp [pi,root,nf,hp,hr,hv]

theorem B_direct {p r v} (hp : nf p = true) (hr : nf r = true)
    (hv : nf v = true) :
    pi ((s ⋆ r ⋆ ((s ⋆ p) ⋆ r)) ⋆ v) =
      (r ⋆ v) ⋆ (((s ⋆ p) ⋆ r) ⋆ v) := by
  simp [pi,root,nf,hp,hr,hv]

/-- At the second round, the scanner p v and a fresh copy of r v are
    simultaneous siblings, while the direct continuation has already advanced. -/
theorem B_delayed {p r v} (hp : nf p = true) (hr : nf r = true)
    (hv : nf v = true) :
    rounds 2 ((s ⋆ r ⋆ ((s ⋆ p) ⋆ r)) ⋆ v) =
      pi (r ⋆ v) ⋆ ((p ⋆ v) ⋆ (r ⋆ v)) := by
  change pi (pi _) = _
  rw [B_direct hp hr hv]
  change (if nf (r ⋆ v) && nf (((s ⋆ p) ⋆ r) ⋆ v) then _ else _) = _
  have hno : nf (((s ⋆ p) ⋆ r) ⋆ v) = false := by simp [nf,root]
  simp only [hno,Bool.and_false,Bool.false_eq_true,ite_false]
  congr 1
  simp [pi,nf,root,hp,hr,hv]

theorem rounds_fixed {t} (h : nf t = true) (n) : rounds n t = t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rounds, fixed h, ih]

theorem rounds_add (m n : Nat) (t : Term) :
    rounds (m+n) t = rounds n (rounds m t) := by
  induction m generalizing t with
  | zero => simp [rounds]
  | succ m ih => simp [Nat.succ_add,rounds,ih]

theorem occ_nonNormal {a t} (o : Occ a t) (hn : nf a = false) : nf t = false := by
  induction o with
  | here => exact hn
  | left h ih => simp [nf,ih]
  | right h ih => simp [nf,ih]

theorem occ_round {a t} (o : Occ a t) (hn : nf a = false) : Occ (pi a) (pi t) := by
  induction o with
  | here => exact .here
  | left h ih =>
    have fc := occ_nonNormal h hn
    simp only [pi,fc,Bool.false_and,Bool.false_eq_true,ite_false]
    exact .left ih
  | right h ih =>
    have fc := occ_nonNormal h hn
    simp only [pi,fc,Bool.and_false,Bool.false_eq_true,ite_false]
    exact .right ih

/-- A future nonnormal descendant in a tracked subtree also occurs at that
    same age in the whole tree. Its activity blocks every ancestor. -/
theorem protect {a t u n} (o : Occ t u) (hit : Occ a (rounds n t)) (hn : nf a = false) :
    Occ a (rounds n u) := by
  induction n generalizing t u with
  | zero => exact hit.trans o
  | succ n ih =>
    have ht : nf t = false := by
      cases e : nf t with
      | false => rfl
      | true =>
        rw [rounds_fixed e] at hit
        have f := occ_nonNormal hit hn
        simp [e] at f
    exact ih (occ_round o ht) hit

inductive Choice where
  | a | bFast | bSlow

def letters : List Choice → List Bool
  | [] => []
  | .a::rest => false :: letters rest
  | .bFast::rest | .bSlow::rest => true :: letters rest

def offset : List Choice → Nat
  | [] => 0
  | .a::rest | .bFast::rest => 1 + offset rest
  | .bSlow::rest => 2 + offset rest

theorem folded_applied_red (g p v : Term) (w : List Bool) :
    nf (folded g p w ⋆ v) = false := by
  cases w with
  | nil => simp [folded,nf,root]
  | cons b w => cases b <;> simp [folded,nf,root]

/-- For arbitrary A/B traversal choices before one selected B, the full pair
    (fresh scanner, fresh continuation) occurs at the stated round of the
    actual maximal parallel innermost trajectory. -/
theorem scannerBirth {g p v} (hg : nf g = true) (hp : nf p = true) (hv : nf v = true)
    (tail : List Bool) (path : List Choice) :
    Occ ((p ⋆ v) ⋆ (folded g p tail ⋆ v))
      (rounds (offset path + 2) (folded g p (letters path ++ true :: tail) ⋆ v)) := by
  have red : nf ((p ⋆ v) ⋆ (folded g p tail ⋆ v)) = false := by
    exact occ_nonNormal (.right .here) (folded_applied_red g p v tail)
  induction path with
  | nil =>
    simp only [letters, List.nil_append, offset, Nat.zero_add, folded]
    rw [B_delayed hp (folded_normal hg hp tail) hv]
    exact .right .here
  | cons c rest ih =>
    let r := folded g p (letters rest ++ true :: tail)
    have hr : nf r = true := folded_normal hg hp _
    cases c with
    | a =>
      simp only [letters, List.cons_append, folded, offset, Nat.add_assoc]
      rw [rounds_add]
      change Occ _ (rounds _ (pi ((s ⋆ (s ⋆ p) ⋆ r) ⋆ v)))
      rw [A_extract hp hr hv]
      exact protect (.right .here) ih red
    | bFast =>
      simp only [letters, List.cons_append, folded, offset, Nat.add_assoc]
      rw [rounds_add]
      change Occ _ (rounds _ (pi ((s ⋆ r ⋆ ((s ⋆ p) ⋆ r)) ⋆ v)))
      rw [B_direct hp hr hv]
      exact protect (.left .here) ih red
    | bSlow =>
      simp only [letters, List.cons_append, folded, offset, Nat.add_assoc]
      rw [rounds_add]
      change Occ _ (rounds _ (rounds 2 ((s ⋆ r ⋆ ((s ⋆ p) ⋆ r)) ⋆ v)))
      rw [B_delayed hp hr hv]
      exact protect (.right (.right .here)) ih red

#print axioms scannerBirth
#print axioms nf_iff_normal
#print axioms prepare
#print axioms B_delayed
end TwoScans.Frames
