import Tags
import Live
import Scan

namespace TwoScans.Shell
open Term Frames Generation

def unary : Nat → Term | 0 => s | n+1 => s ⋆ unary n
def marker := unary 21
def pre := s ⋆ marker
def tagger := pre ⋆ Live.L
def g := gen tagger Live.U
abbrev W := word g
def seed (i : List Bool) := g ⋆ W i
def tag (w : List Bool) := marker ⋆ W w
def body (w : List Bool) (n : Nat) := rounds n (Live.L ⋆ W w)
def shell (w : List Bool) (n : Nat) := tag w ⋆ body w n

theorem tagger_nf : nf tagger = true := by decide
theorem g_nf : nf g = true := by decide
theorem w_nf (w) : nf (W w) = true := word_normal g_nf _
theorem t_nf (w) : nf (tag w) = true := by
  have m : ∃ x, marker = s ⋆ x ∧ nf x = true := ⟨unary 20,rfl,by decide⟩
  obtain ⟨x,h,n⟩ := m
  simp [tag,h,nf,root,n,w_nf]
theorem body_live (w n) : nf (body w n) = false := Live.taggedLaunchLive tagger_nf w n
theorem body_next (w n) : pi (body w n) = body w (n+1) :=
  (rounds_add n 1 _).symm

/-- An executable check of the closed code and of the initial wrappers. -/
def edge (f r : Term) : Bool := decide (
  f ≠ marker ∧ (r = marker → f = s) ∧ (f = pre → r = Live.L) ∧ r ≠ pre)
def static : Term → Bool
  | s => true
  | .app f r => static f && static r && edge f r

theorem static_sub {a t} (ht : static t = true) (o : Occ a t) : static a = true := by
  induction o with
  | here => exact ht
  | left _ ih => simp only [static, Bool.and_eq_true] at ht; exact ih ht.1.1
  | right _ ih => simp only [static, Bool.and_eq_true] at ht; exact ih ht.1.2

theorem static_edge {t f r} (ht : static t = true) (o : Occ (f ⋆ r) t) :
    f ≠ marker ∧ (r = marker → f = s) ∧ (f = pre → r = Live.L) ∧ r ≠ pre := by
  have e := static_sub ht o
  simp only [static,Bool.and_eq_true] at e
  exact of_decide_eq_true e.2

theorem static_g : static g = true := by decide
theorem small_w (w) : size pre < size (W w) := by
  have h : size g < size (W w) := Scan.wordSize g w
  have h' : size pre < size g := by decide
  omega

theorem static_w (w) : static (W w) = true := by
  induction w with
  | nil => exact (by decide : static (s ⋆ g) = true)
  | cons b w ih =>
    rw [show W (b::w) = op b ⋆ W w from addWord g b w]
    have small := small_w w
    have sm : size marker < size pre := by decide
    have r1 : W w ≠ marker := by intro e; rw [e] at small; omega
    have r2 : W w ≠ pre := by intro e; rw [e] at small; omega
    have n1 : op b ≠ marker := by cases b <;> decide
    have n2 : op b ≠ pre := by cases b <;> decide
    have ok : static (op b) = true := by cases b <;> decide
    simp [static,edge,ih,ok,n1,n2,r1,r2]

theorem static_seed (i) : static (seed i) = true := by
  have small := small_w i
  have sm : size marker < size pre := by decide
  have r1 : W i ≠ marker := by intro e; rw [e] at small; omega
  have r2 : W i ≠ pre := by intro e; rw [e] at small; omega
  have n1 : g ≠ marker := by decide
  have n2 : g ≠ pre := by decide
  simp [seed,static,edge,static_g,static_w,n1,n2,r1,r2]

theorem rightMarker {t} (h : static t = true) : RightOnly marker pre t := by
  intro f o; rw [(static_edge h o).2.1 rfl]; rfl
theorem noPrefix {t} (h : static t = true) : NoRight pre t := by
  intro f o; exact (static_edge h o).2.2.2 rfl
theorem leftPrefix {t} (h : static t = true) : LeftOnly pre Live.L t := by
  intro a o; exact (static_edge h o).2.2.1 rfl

theorem word_injective {u v : List Bool} (h : W u = W v) : u = v := by
  induction u generalizing v with
  | nil => cases v with
           | nil => rfl
           | cons b v => cases b <;> cases h
  | cons b u ih =>
    cases v with
    | nil => cases b <;> cases h
    | cons c v => cases b <;> cases c <;> cases h' : decEq u v with
      | isTrue eq => subst v; first | rfl | cases h
      | isFalse ne => first | cases h | exact False.elim (ne (ih ((Term.app.inj h).2)))

theorem anchored_word {i w : List Bool} (h : Occ (W i) (W w)) : ∃ extra, w = extra ++ i := by
  have big : size g < size (W i) := Scan.wordSize g i
  induction w with
  | nil =>
    rcases h.appCases with self | hs | hg
    · exact ⟨[],(word_injective self).symm⟩
    · have hn := hs.sizeLE
      have small : size s ≤ size g := by decide
      omega
    · have := hg.sizeLE; omega
  | cons b w ih =>
    rw [show W (b::w) = op b ⋆ W w from addWord g b w] at h
    rcases h.appCases with self | hl | hr
    · rw [← addWord] at self; exact ⟨[],(word_injective self).symm⟩
    · have := hl.sizeLE; have small : size (op b) ≤ size g := by cases b <;> decide
      omega
    · obtain ⟨extra,rfl⟩ := ih hr
      exact ⟨b::extra,rfl⟩

/-- Naked word tags are excluded by the ordinary application rule. The one
    exception pairs a valid tag with the actual body of that packet at its age.
    Non-word tags may circulate, but their operand is already normal. -/
inductive Clean (initial : List Bool) : Term → Prop where
  | atom : Clean initial s
  | node {f r} : Clean initial f → Clean initial r →
      (f = marker → nf r = true) → (f = marker → ∀ w, r ≠ W w) →
      Clean initial (f ⋆ r)
  | packet (extra : List Bool) (n : Nat) : Clean initial (body (extra ++ initial) n) →
      Clean initial (shell (extra ++ initial) n)

theorem cleanStatic {i t} (h : static t = true) : Clean i t := by
  induction t with
  | s => exact .atom
  | app f r ihf ihr =>
    have ne := (static_edge h .here).1
    exact .node (ihf (static_sub h (.left .here))) (ihr (static_sub h (.right .here)))
      (fun eq => False.elim (ne eq)) (fun eq => False.elim (ne eq))

theorem Clean.pair {i f r} (a : Clean i f) (b : Clean i r) (ne : f ≠ marker) :
    Clean i (f ⋆ r) := .node a b (fun eq => False.elim (ne eq)) (fun eq => False.elim (ne eq))

theorem Clean.normalChildren {i f r} (a : Clean i (f ⋆ r)) (hn : nf (f ⋆ r) = true) :
    Clean i f ∧ Clean i r := by
  cases a with
  | node hf hr _ _ => exact ⟨hf,hr⟩
  | packet extra n _ =>
    have red := body_live (extra ++ i) n
    simp only [nf, red, Bool.and_false] at hn
    contradiction

theorem smallPi {i t} (h : Safe g (W i) t) (eq : pi t = marker) : t = marker := by
  cases h with
  | origL o => rwa [fixed ((nf_iff_normal _).2 (((nf_iff_normal _).1 g_nf).sub o))] at eq
  | origR o => rwa [fixed ((nf_iff_normal _).2 (((nf_iff_normal _).1 (w_nf i)).sub o))] at eq
  | @join a b _ _ o =>
    have sz := o.sizeLE
    have small := small_w i
    have lt : size marker < size pre := by decide
    have mono := Live.stepSizes (piSteps (a ⋆ b))
    rw [eq] at mono
    simp only [size] at mono
    omega

theorem root_new {i x y z} (hs : Safe g (W i) (s ⋆ x ⋆ y ⋆ z))
    (pref : LeftOnly pre Live.L (s ⋆ x ⋆ y ⋆ z))
    (cx : Clean i x) (cy : Clean i y) (cz : Clean i z) (nz : nf z = true) :
    Clean i ((x ⋆ z) ⋆ (y ⋆ z)) := by
  have cutoff := Safe.cut ((nf_iff_normal _).1 g_nf) ((nf_iff_normal _).1 (w_nf i)) hs (.root x y z)
  have small : size marker < size (W i) := Nat.lt_trans (by decide : size marker < size pre) (small_w i)
  have left_ne : x ⋆ z ≠ marker := by
    intro eq
    have zl := cutoff.sizeLE
    have large : size z < size (x ⋆ z) := by have h := sizePos x; simp only [size]; omega
    rw [eq] at large
    omega
  by_cases newTag : x = marker ∨ y = marker
  · obtain ⟨rfl,rfl⟩ := uniqueTagProducer hs small (rightMarker static_g) (rightMarker (static_w i)) pref newTag
    have launchNe : Live.L ≠ marker := by decide
    have launch := cy.pair cz launchNe
    by_cases wordArg : ∃ w, z = W w
    · obtain ⟨w,rfl⟩ := wordArg
      obtain ⟨extra,rfl⟩ := anchored_word cutoff
      exact .packet extra 0 launch
    · exact (Clean.node cx cz (fun _ => nz) (fun _ w h => wordArg ⟨w,h⟩)).pair launch left_ne
  · exact (cx.pair cz (fun h => newTag (.inl h))).pair
          (cy.pair cz (fun h => newTag (.inr h))) left_ne

theorem clean_pi {i t} (hs : Safe g (W i) t) (pref : LeftOnly pre Live.L t)
    (old : Clean i t) : Clean i (pi t) := by
  induction t with
  | s => exact old
  | app f r ihf ihr =>
    cases old with
    | node cf cr tagNF tagNo =>
      by_cases children : nf f && nf r
      · simp only [pi,children,ite_true]
        cases f with
        | s => exact .node cf cr tagNF tagNo
        | app a y =>
          cases a with
          | s => exact .node cf cr tagNF tagNo
          | app hd x =>
            cases hd with
            | app _ _ => exact .node cf cr tagNF tagNo
            | s =>
              have both : nf (s ⋆ x ⋆ y) = true ∧ nf r = true := by simpa only [Bool.and_eq_true] using children
              have fn := (nf_iff_normal _).1 both.1
              have sx := (nf_iff_normal _).2 (fn.sub (Occ.left Occ.here))
              have c := cf.normalChildren both.1
              exact root_new hs pref (c.1.normalChildren sx).2 c.2 cr both.2
      · simp only [pi,children]
        have a := ihf hs.children.1 (fun b o => pref b (.left o)) cf
        have b := ihr hs.children.2 (fun c o => pref c (.right o)) cr
        apply Clean.node a b
        · intro h
          have m := smallPi hs.children.1 h
          rw [fixed (tagNF m)]
          exact tagNF m
        · intro h
          have m := smallPi hs.children.1 h
          rw [fixed (tagNF m)]
          exact tagNo m
    | packet extra n cp =>
      have nb := body_live (extra ++ i) n
      simp only [pi,nb,Bool.and_false,Bool.false_eq_true,ite_false,fixed (t_nf _),body_next]
      apply Clean.packet
      rw [← body_next]
      exact ihr hs.children.2 (fun _ o => pref _ (.right o)) cp

theorem clean_orbit (i : List Bool) (n : Nat) : Clean i (rounds n (seed i)) := by
  have init : Safe g (W i) (seed i) := .join (.origL .here) (.origR .here) .here
  have ng := (nf_iff_normal _).1 g_nf
  have nw := (nf_iff_normal _).1 (w_nf i)
  have nl : Normal Live.L := (nf_iff_normal _).1 (by decide)
  induction n with
  | zero => exact cleanStatic (static_seed i)
  | succ n ih =>
    rw [rounds_add n 1]; change Clean i (pi (rounds n (seed i)))
    have steps := roundsSteps (seed i) n
    apply clean_pi (keepsSafe ng nw init steps) _ ih
    exact leftOnlySteps ng nw nl (small_w i) (noPrefix static_g) (noPrefix (static_w i))
            steps init (leftPrefix (static_seed i))

theorem Clean.ne_tag {i t} (h : Clean i t) (w) : t ≠ tag w := by
  intro he
  cases h with
  | atom => cases he
  | node _ _ _ forb =>
    obtain ⟨fg,rg⟩ := Term.app.inj he
    exact forb fg w rg
  | packet extra n cp =>
    have eq := (Term.app.inj he).1
    have large := small_w (extra ++ i)
    have sm : size marker < size pre := by decide
    have blow : size marker < size (tag (extra ++ i)) := by simp [tag,size]; exact sizePos _
    rw [eq] at blow
    omega

theorem applies_tag_red (w r) : nf (tag w ⋆ r) = false := by rfl

theorem Clean.readShell {i t} (h : Clean i t) {w r} (o : Occ (tag w ⋆ r) t) :
    ∃ extra age, w = extra ++ i ∧ r = body w age := by
  induction h with
  | atom => cases o
  | node a b _ _ iha ihb =>
    rcases o.appCases with self | left | right
    · exact False.elim ((a.ne_tag w) (Term.app.inj self).1.symm)
    · exact iha left
    · exact ihb right
  | packet extra n _ ih =>
    rcases o.appCases with self | left | right
    · obtain ⟨h1,h2⟩ := Term.app.inj self
      have wi := word_injective ((Term.app.inj h1).2)
      exact ⟨extra,n,wi,wi ▸ h2⟩
    · have impossible := occ_nonNormal left (applies_tag_red w r)
      rw [t_nf] at impossible
      contradiction
    · exact ih right

theorem shell_pi (w n) : pi (shell w n) = shell w (n+1) := by
  simp [shell,pi,body_live,t_nf,fixed (t_nf _),body_next]

theorem shell_after (w n) : rounds n (shell w 0) = shell w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rounds_add n 1, ih]; exact shell_pi w n

theorem shell_zero (w) : pi (tagger ⋆ W w) = shell w 0 := by
  have m : nf marker = true := by decide
  have nl : nf Live.L = true := by decide
  simp [tagger,pre,tag,shell,body,rounds,pi,nf,root,m,nl,w_nf]

theorem shell_visible (i extra : List Bool) (age : Nat) : Visible (seed i) (shell (extra ++ i) age) := by
  apply (everyExtension tagger_nf (by decide : nf Live.U = true) i extra).trans
  apply Visible.tick
  change Visible (pi (tagger ⋆ W (extra ++ i))) (shell (extra ++ i) age)
  rw [shell_zero]
  exact ⟨age,by rw [shell_after] ; exact .here⟩

/-- A complete characterization for every input suffix and every putative
    shell in the unbounded orbit of its ground pure-S seed. -/
theorem shell_orbit_iff (i w : List Bool) (r : Term) :
    Visible (seed i) (tag w ⋆ r) ↔ ∃ extra age, w = extra ++ i ∧ r = body w age := by
  constructor
  · rintro ⟨n,o⟩
    exact (clean_orbit i n).readShell o
  · rintro ⟨extra,age,rfl,rfl⟩
    exact shell_visible i extra age

#print axioms shell_orbit_iff
end TwoScans.Shell
