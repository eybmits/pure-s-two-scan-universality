import ShellAnyTape
import WordRead

namespace TwoScans.Readback
open Automata WordRead Shell Frames Select

/-- A suffix retains the output automaton's state for every possible
    incoming transducer state. The state table is finite even on malformed words. -/
theorem stream_attribute {Q Y V : Type} [FinStates Q] (r : OutputStream.Reader Q Y)
    (s : Q) {query : List Y → V} (hq : Attr query) :
    Attr (fun w => query (OutputStream.transduce r s w)) := by
  classical
  obtain ⟨K,ik,k,d,a,ok⟩ := hq
  haveI := ik
  letI : Inhabited K := ⟨k⟩
  let step (b : Bool) (next : Q → K) (q : Q) :=
    let (q',out) := r.transition q b
    match out with | none => next q' | some y => d y (next q')
  have eq (w : List Bool) (q : Q) :
      (w.foldr step (fun _ => k)) q = (OutputStream.transduce r q w).foldr d k := by
    induction w generalizing q with
    | nil => rfl
    | cons b w ih =>
      simp only [List.foldr_cons,OutputStream.transduce]
      change step b _ q = _
      cases e : r.transition q b with | mk h y => cases y <;> simp [step,e,ih,Option.elim]
  exact ⟨Q → K,inferInstance,fun _ => k,step,fun f => a (f s),fun w => by dsimp only; rw [eq,ok]⟩

private theorem andReg {P R : Term → Prop} (p : Regular P) (r : Regular R) :
    Regular (fun t => P t ∧ R t) := by
  obtain ⟨A,ia,a,f,fa⟩ := p
  obtain ⟨B,ib,b,g,gb⟩ := r
  haveI := ia
  haveI := ib
  exact ⟨_,inferInstance,a.zip b,(fun (x,y) => f x && g y),fun t => by simp [Fold.zip_run,fa,gb]⟩

private theorem attrWords {f : List Bool → Bool} (h : Attr f) :
    Regular (fun t => ∃ w, t = W w ∧ f w = true) := by
  obtain ⟨K,ik,k,d,a,eq⟩ := h
  haveI := ik
  obtain ⟨U,iu,m,e,h⟩ := regular_word g k d a
  exact ⟨U,iu,m,e,fun t => by rw [h]; simp only [eq,W]⟩

/-- Regular tests on the first result cannot be replaced by an arbitrary
    later success. This priority fold stores 'no hit', 'failed query' or
    'passed query' and chooses the root before either child. -/
theorem first_preimage {Y} (read : Term → Option Y) (query : Y → Bool)
    (anyHit : Regular (fun t => ∃ y, read t = some y))
    (goodHit : Regular (fun t => ∃ y, read t = some y ∧ query y = true)) :
    Regular (fun t => ∃ y, first read t = some y ∧ query y = true) := by
  obtain ⟨A,ia,a,ok,ha⟩ := anyHit
  obtain ⟨B,ib,b,test,hb⟩ := goodHit
  haveI := ia
  haveI := ib
  let kernel := a.zip b
  let localValue (q : A × B) := if ok q.1 then some (test q.2) else none
  have localOK (t) : localValue (kernel.run t) = (read t).map query := by
    rw [show kernel.run t = _ from Fold.zip_run ..]
    cases e : read t with
    | none =>
      have hn : ok (a.run t) = false := by
        cases k : ok (a.run t) with | false => rfl | true => obtain ⟨_,h⟩ := (ha t).mp k; rw [e] at h; cases h
      simp [localValue,hn]
    | some y =>
      have h := (ha t).mpr ⟨y,e⟩
      cases p : query y with
      | true => simp [localValue,h,(hb t).mpr ⟨y,e,p⟩,p]
      | false =>
        have hn : test (b.run t) = false := by
          cases k : test (b.run t) with
          | false => rfl
          | true =>
            obtain ⟨z,eq,zp⟩ := (hb t).mp k
            have yz := Option.some.inj (e.symm.trans eq)
            subst z; rw [p] at zp; cases zp
        simp [localValue,h,hn,p]
  let f := kernel.extend (localValue kernel.leaf)
    (fun l r => (localValue (kernel.fork l.1 r.1)).or (l.2.or r.2))
  have spec (t : Term) : (f.run t).2 = (first read t).map query := by
    induction t with
    | s => exact localOK Term.s
    | app l r il ir =>
      change (localValue (kernel.fork (f.run l).1 (f.run r).1)).or ((f.run l).2.or (f.run r).2) = _
      rw [show (f.run l).1 = _ from Fold.extend_base ..,show (f.run r).1 = _ from Fold.extend_base ..,il,ir]
      change (localValue (kernel.run (.app l r))).or _ = _
      rw [localOK]; simp only [first]
      cases read (.app l r) <;> cases first read l <;> rfl
  refine ⟨_,inferInstance,f,(fun z => z.2.getD false),?_⟩
  intro t; dsimp only; rw [spec]
  cases e : first read t <;> simp

theorem local_preimage {Y} (wp bp) (value : List Bool → Y) (query : Y → Bool)
    (wordReg : Regular (fun t => ∃ w, t = W w ∧ wp w = true))
    (bodyReg : Regular (fun t => bp t = true))
    (queried : Attr (fun w => query (value w))) :
    Regular (fun t => ∃ y, first (localReport wp bp value) t = some y ∧ query y = true) := by
  apply first_preimage _ _ (regular_local wp bp value wordReg bodyReg)
  let changed := fun w => wp w && query (value w)
  obtain ⟨K,ik,k,f,hk⟩ := andReg wordReg (attrWords queried)
  have rwrd : Regular (fun t => ∃ w, t = W w ∧ changed w = true) := by
    refine ⟨K,ik,k,f,fun t => ?_⟩
    rw [hk]
    constructor
    · rintro ⟨⟨w,rfl,hw⟩,v,ev,hv⟩
      have z := word_injective ev
      subst v; exact ⟨w,rfl,by simp [changed,hw,hv]⟩
    · rintro ⟨w,rfl,h⟩
      have z : wp w = true ∧ query (value w) = true := by simpa [changed] using h
      exact ⟨⟨_,rfl,z.1⟩,_,rfl,z.2⟩
  obtain ⟨U,iu,m,p,hm⟩ := regular_local changed bp value rwrd bodyReg
  refine ⟨U,iu,m,p,fun t => ?_⟩
  rw [hm]
  constructor
  · rintro ⟨y,ok⟩
    obtain ⟨w,r,et,pass,src,eq⟩ := (localReport_iff _ _ _ _ _).mp ok
    have z : wp w = true ∧ query (value w) = true := by simpa [changed] using pass
    exact ⟨y,(localReport_iff _ _ _ _ _).mpr ⟨w,r,et,z.1,src,eq⟩,eq ▸ z.2⟩
  · rintro ⟨y,ok,queryY⟩
    obtain ⟨w,r,et,pass,src,eq⟩ := (localReport_iff _ _ _ _ _).mp ok
    exact ⟨y,(localReport_iff _ _ _ _ _).mpr
      ⟨w,r,et,by simp [changed,eq,pass,queryY],src,eq⟩⟩

end TwoScans.Readback

namespace TwoScans.AnyTape
open Readback Automata WordRead Frames Shell Tableau Tableau.OneTape
/-- Every finite-state output query has a regular inverse image on *all*
    pure-S trees, using the actual first-shell decoder. -/
theorem report_preimage {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [FinStates Q] [FinStates Γ]
    (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (query : List (Color Q Γ) → Bool)
    (h : Attr query) :
    Regular (fun t => ∃ row, AnyTape.report δ blank halt t = some row ∧ query row = true) := by
  apply local_preimage _ _ _ _ _ (Join.regular_both ..)
    (stream_attribute _ _ h)
  have langs := Static.reg_wordOK (AnyTape.A Q Γ) [] (AnyTape.siteTest δ blank halt)
    ⟨_,inferInstance,.tail false .empty,Static.advance (AnyTape.liftRule δ blank)
      (AnyTape.haltColor halt ∘ AnyTape.erase blank) AnyTape.Mode.empty AnyTape.readIn,
      Static.done AnyTape.inOK,fun _ => Iff.rfl⟩
  obtain ⟨K,ik,q,d,a,hk⟩ := langs
  haveI := ik
  obtain ⟨N,iN,fold,p,hn⟩ := regular_word g q d a
  exact ⟨_,iN,fold,p,fun t => by rw [hn]; simp only [hk,AnyTape.wordTest,W]⟩

#print axioms TwoScans.Readback.stream_attribute
#print axioms report_preimage
end TwoScans.AnyTape
