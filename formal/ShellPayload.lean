import PayloadBits
import ShellBlockLanguage
import ShellStatic

namespace TwoScans.Static
open WordBlocks TrackLayout PayloadBits Automata Language
open Label
variable {U C : Type}

/-- Drop the initial B run and its delimiter. -/
def strip : List Bool → Nat × List Bool
  | [] => (0,[])
  | false :: xs => (0,xs)
  | true :: xs => let (n,r) := strip xs; (n+1,r)

theorem strip_prefix (k : Nat) (v : List Bool) : strip (List.replicate k true ++ false :: v) = (k,v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,strip,ih]

def readLabels [FinStates (Label U C)] (A : Alphabet (Label U C))
    (foot raw : List Bool) : List (Label U C) :=
  let rest := (strip raw).2
  let code := rest.take (rest.length - foot.length)
  let result := code.foldr (bitStep A List.cons) (some (cleanBuf A.width,[]))
  match result with | some (_,xs) => xs | none => []

private theorem stripped_payload (A : Alphabet (Label U C)) (us : List U) (vs : List C) (w : Nat) (f) :
    strip (payload A us vs w f) = (w*A.width,chunks A (bodyLabels us vs) ++ f) := by
  simpa [payload,List.append_assoc] using strip_prefix (w*A.width) (chunks A (bodyLabels us vs) ++ f)

theorem readLabels_payload [FinStates (Label U C)] (A : Alphabet (Label U C)) (us : List U)
    (vs : List C) (w : Nat) (f) : readLabels A f (payload A us vs w f) = bodyLabels us vs := by
  simp only [readLabels,stripped_payload,List.length_append,Nat.add_sub_cancel,List.take_left]
  rw [chunks_fold]
  exact List.foldr_cons_nil

def sitesOf [FinStates (Label U C)] (A : Alphabet (Label U C)) (foot raw : List Bool) : List U :=
  (readLabels A foot raw).filterMap (fun | .site u => some u | _ => none)
def colorsOf [FinStates (Label U C)] (A : Alphabet (Label U C)) (foot raw : List Bool) : List C :=
  ((readLabels A foot raw).filterMap (fun | .color c => some c | _ => none)).reverse

theorem sitesOf_payload [FinStates (Label U C)] (A : Alphabet (Label U C)) (us : List U)
    (vs : List C) (w : Nat) (f) : sitesOf A f (payload A us vs w f) = us := by
  simp [sitesOf,readLabels_payload,bodyLabels,List.filterMap_map,Function.comp_def]
theorem colorsOf_payload [FinStates (Label U C)] (A : Alphabet (Label U C)) (us : List U)
    (vs : List C) (w : Nat) (f) : colorsOf A f (payload A us vs w f) = vs := by
  simp [colorsOf,readLabels_payload,bodyLabels,List.filterMap_map,Function.comp_def]

def widthOf (A : Alphabet (Label U C)) (raw : List Bool) := (strip raw).1 / A.width
theorem widthOf_payload (A : Alphabet (Label U C)) (us : List U)
    (vs : List C) (w : Nat) (f) : widthOf A (payload A us vs w f) = w := by
  simp [widthOf,stripped_payload,Nat.mul_div_cancel _ A.positive]

/-- Executable specification. An independent construction below compiles this
    language to finite control, so the raw reserialization is optional. -/
def wordOK [FinStates (Label U C)] (A : Alphabet (Label U C)) (foot : List Bool)
    (siteOK : List U → Bool) (raw : List Bool) : Bool :=
  let us := sitesOf A foot raw
  let vs := colorsOf A foot raw
  let w := widthOf A raw
  decide (raw = payload A us vs w foot ∧ 0 < w) && siteOK us

theorem wordOK_iff [FinStates (Label U C)] (A : Alphabet (Label U C)) (foot : List Bool)
    (siteOK : List U → Bool) (raw : List Bool) :
    wordOK A foot siteOK raw = true ↔
      ∃ us vs w, raw = payload A us vs w foot ∧ 0 < w ∧ siteOK us = true := by
  constructor
  · intro h
    simp only [wordOK,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨_,_,_,h.1.1,h.1.2,h.2⟩
  · rintro ⟨us,vs,w,rfl,hw,ok⟩
    simp [wordOK,sitesOf_payload,colorsOf_payload,widthOf_payload,hw,ok]

private def siteLabel : Label U C → Option U | .site x => some x | _ => none
private def colorLabel : Label U C → Option C | .color x => some x | _ => none

theorem body_regular [DecidableEq U] [DecidableEq C] (ok : List U → Bool)
    (h : Reg (fun us => ok us = true)) :
    Reg (fun ls : List (Label U C) => ∃ us vs, ls = bodyLabels us vs ∧ ok us = true) := by
  have ru := mapped (Label.site (C:=C)) siteLabel (by intro x y; cases x <;> simp [siteLabel]) h
  have rv := mapped (Label.color (U:=U)) colorLabel (by intro x y; cases x <;> simp [colorLabel]) (unrestricted C)
  let m := concatenate (single (ub : Label U C)) (concatenate ru (concatenate (exactWord [ue,ve]) (concatenate rv (single vb))))
  apply congruence m
  intro ls
  constructor
  · rintro ⟨_,_,rfl,rfl,_,_,rfl,⟨us,rfl,good⟩,_,_,rfl,rfl,_,_,rfl,⟨vs,rfl,_⟩,rfl⟩
    exact ⟨us,vs.reverse,by simp [bodyLabels,List.append_assoc],good⟩
  · rintro ⟨us,vs,rfl,good⟩
    refine ⟨_,_,?_,rfl,_,_,rfl,⟨us,rfl,good⟩,_,_,rfl,rfl,_,_,rfl,⟨vs.reverse,rfl,trivial⟩,rfl⟩
    simp [bodyLabels,List.append_assoc]

private def unaryBlock {α} (A : Alphabet α) : Alphabet Unit :=
  ⟨A.width,A.positive,(fun _ => List.replicate A.width true),(fun _ => by simp),(fun () () _ => rfl)⟩

private theorem copies {α} (A : Alphabet α) (n : List Unit) :
    chunks (unaryBlock A) n = List.replicate (n.length * A.width) true := by
  induction n with
  | nil => simp [chunks]
  | cons x xs ih =>
    change List.replicate A.width true ++ chunks (unaryBlock A) xs = _
    rw [ih,List.replicate_append_replicate]
    simp [Nat.add_mul,Nat.add_comm]

theorem regular_header {α} (A : Alphabet α) :
    Reg (fun raw : List Bool => ∃ w, 0 < w ∧ raw = List.replicate (w*A.width) true) := by
  have nonempty : Reg (fun w : List Unit => w ≠ []) :=
    ⟨Bool,inferInstance,false,fun _ _ => true,id,fun w => by cases w <;> simp⟩
  apply congruence (coded (unaryBlock A) nonempty)
  intro raw
  constructor
  · rintro ⟨v,rfl,hv⟩; exact ⟨v.length,List.length_pos_iff.mpr hv,copies _ _⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨List.replicate w (),by simp [copies],by intro e; have h := congrArg List.length e; simp at h; omega⟩

theorem reg_wordOK [DecidableEq U] [DecidableEq C] [FinStates (Label U C)]
    (A : Alphabet (Label U C)) (foot : List Bool) (ok : List U → Bool)
    (h : Reg (fun us => ok us = true)) : Reg (fun raw => wordOK A foot ok raw = true) := by
  let shape := concatenate (regular_header A) (concatenate (single false) (concatenate (coded A (body_regular ok h)) (exactWord foot)))
  apply congruence shape
  intro raw
  rw [wordOK_iff]
  constructor
  · rintro ⟨_,_,rfl,⟨w,hw,rfl⟩,_,_,rfl,rfl,_,_,rfl,⟨_,rfl,us,vs,rfl,good⟩,rfl⟩
    exact ⟨us,vs,w,by simp [payload,List.append_assoc],hw,good⟩
  · rintro ⟨us,vs,w,rfl,hw,good⟩
    refine ⟨_,_,?_,⟨w,hw,rfl⟩,_,_,rfl,rfl,_,_,rfl,⟨_,rfl,us,vs,rfl,good⟩,rfl⟩
    simp [payload,List.append_assoc]

#print axioms reg_wordOK
#print axioms sitesOf_payload
end TwoScans.Static
