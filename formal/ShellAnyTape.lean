import ShellAnyInput
import ShellSelectedRead

set_option linter.unusedSectionVars false
namespace TwoScans.AnyTape
open Automata WordBlocks TrackLayout PayloadBits Tableau OneTape Frames Shell

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [FinStates Q] [FinStates Γ]
abbrev A (Q Γ : Type) [DecidableEq Q] [DecidableEq Γ] [FinStates Q] [FinStates Γ] :=
  FiniteCodes.alphabet (L (Color Q Γ))
abbrev erase (blank : Γ) : Mark (Color Q Γ) → Color Q Γ := forget (.plain blank) .wall
abbrev liftRule (δ : Table Q Γ) (blank : Γ) := markedRule (rule δ) (.plain blank) .wall

def core (c : Cfg Q Γ) : List (Color Q Γ) :=
  c.left.reverse.map .plain ++ .head c.state c.here :: c.right.map .plain

def startTerm (_blank : Γ) (c : Cfg Q Γ) := seed (key (A Q Γ) (core c))

def haltColor (halt : Q → Bool) : Color Q Γ → Bool | .head q _ => halt q | _ => false
def siteTest (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (u : List (Site (Mark (Color Q Γ)))) :=
  Static.done inOK (u.foldr (Static.advance (liftRule δ blank) (haltColor halt ∘ erase blank)
    Mode.empty readIn) (.tail false .empty))
def wordTest (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) :=
  Static.wordOK (A Q Γ) [] (siteTest δ blank halt)

abbrev bodyTest := Join.both (A Q Γ) Site.current Site.expected []
def projection (blank : Γ) : Site (Mark (Color Q Γ)) → Option (Color Q Γ)
  | .finalCell c => some (erase blank c)
  | _ => none
def getRow (blank : Γ) := OutputStream.transduce (OutputStream.reader (A Q Γ) (projection blank)) .header
def report (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) :=
  first (localReport (wordTest δ blank halt) (bodyTest (Q:=Q) (Γ:=Γ)) (getRow (Q:=Q) blank))

private theorem staticRows (δ : Table Q Γ) (blank : Γ) (halt) (u) :
    siteTest δ blank halt u = true ↔ ∃ b last k input, u = writeSites b last ∧
      (∀ r ∈ b, tileCheck (liftRule δ blank) none r = true) ∧
      last.any (haltColor halt ∘ erase blank) = true ∧
      (b.map (List.map Tile.center) ++ [last]).head? = some (initialRow input k) := by
  unfold siteTest; rw [Static.rows_iff]
  have head (b : List (List (Tile (Mark (Color Q Γ))))) (last : List (Mark (Color Q Γ))) :
      (b.map (List.map Tile.center) ++ [last]).head? = some ((b.head?.map (List.map Tile.center)).getD last) := by
    cases b <;> rfl
  simp only [List.all_eq_true,input_iff,head,Option.some.injEq]
  constructor
  · rintro ⟨b,last,hu,hl,hf,x,k,hx⟩; exact ⟨b,last,k,x,hu,hl,hf,hx⟩
  · rintro ⟨b,last,k,x,hu,hl,hf,hx⟩; exact ⟨b,last,hu,hl,hf,x,k,hx⟩

private theorem out_write (blank : Γ) (b : List (List (Tile (Mark (Color Q Γ))))) last :
    (writeSites b last).filterMap (projection blank) = last.map (erase blank) := by
  have pre (r : List (Tile (Mark (Color Q Γ)))) : (preSites r).filterMap (projection blank) = [] := by
    simp [preSites,projection]
  induction b with
  | nil =>
    change (last.map Site.finalCell).filterMap (projection blank) = last.map (erase blank)
    induction last with | nil => rfl | cons c cs ih => exact congrArg (List.cons _) ih
  | cons r rs ih =>
    have e : writeSites (r::rs) last = preSites r ++ writeSites rs last := by simp [writeSites,List.append_assoc]
    simp [e,List.filterMap_append,pre,ih]

private theorem regular_wordTest (δ : Table Q Γ) (blank : Γ) (halt) :
    Regular (fun t => ∃ w, t = W w ∧ wordTest δ blank halt w = true) := by
  have langs := Static.reg_wordOK (A Q Γ) [] (siteTest δ blank halt)
    ⟨_,inferInstance,.tail false .empty,Static.advance (liftRule δ blank) (haltColor halt ∘ erase blank)
      Mode.empty readIn,Static.done inOK, fun _ => Iff.rfl⟩
  obtain ⟨K,ik,k,d,a,h⟩ := langs
  haveI := ik
  obtain ⟨M,im,m,p,hm⟩ := regular_word g k d a
  exact ⟨M,im,m,p,fun t => by rw [hm]; simp only [h,wordTest,W]⟩

theorem report_regular (δ : Table Q Γ) (blank : Γ) (halt) :
    Regular (fun t => ∃ row, report δ blank halt t = some row) :=
  regular_first _ _ _ (regular_wordTest δ blank halt) (Join.regular_both ..)

/-- The actual full-row reporter admits one finite bottom-up annotation, one
    selector path, and one ordinary output transducer on that shell's word.
    The selected output pass never reruns the machine/scan tests. -/
theorem streamed_report (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) :
    ∃ (K : Type) (_ : FinStates K) (a : Fold K) (yes : K → Bool), ∀ t,
      (Select.select yes (Select.decorate (Select.marks a yes) t)).bind
          (fun n => Select.selectedRead (getRow (Q:=Q) blank) n.erase) = report δ blank halt t := by
  exact Select.select_without_retest _ _ _ (regular_wordTest δ blank halt) (Join.regular_both ..)

private theorem decode_data (δ : Table Q Γ) (blank : Γ) (halt) (c : Cfg Q Γ) (j : Nat) (row)
    (h : report δ blank halt (rounds j (startTerm blank c)) = some row) :
    ∃ n k, let last := run (sweep (liftRule δ blank) none) (initialRow (core c) k) n
           last.any (haltColor halt ∘ erase blank) = true ∧ last.map (erase blank) = row := by
  obtain ⟨pre,age,wp,bp,val⟩ := first_output_sound _ _ _ _ _ _ h
  obtain ⟨us,vs,w,hwrd,hw,st⟩ := (Static.wordOK_iff _ [] _ _).1 wp
  rw [hwrd] at bp val
  have probes := (Join.both_iff (A Q Γ) (FiniteCodes.wide _) FiniteCodes.starts FiniteCodes.ends
    [] us vs w hw).mp ⟨age,bp⟩
  obtain ⟨b,last,k,inp,rfl,tiles,done,head⟩ := (staticRows _ _ _ _).mp st
  obtain ⟨other,haveKey⟩ := genuine_key (A Q Γ) inp k _ _ _ _ head probes
  have id := key_unique (A Q Γ) (core c) inp pre other (hwrd.trans haveKey)
  subst inp
  have checked := tableau_tracks_sound (liftRule δ blank) _ b last hw head tiles probes
  have eq := siteCheck_sound _ _ _ _ _ checked
  refine ⟨b.length,k,?_⟩
  dsimp only; rw [←eq]
  refine ⟨done,?_⟩
  simpa only [getRow,OutputStream.on_payload (A Q Γ) FiniteCodes.ends,out_write] using val

private theorem encode_data (δ : Table Q Γ) (blank : Γ) (halt) (c : Cfg Q Γ) (n k : Nat)
    (hit : (run (sweep (liftRule δ blank) none) (initialRow (core c) k) n).any
       (haltColor halt ∘ erase blank) = true) :
    ∃ j row, report δ blank halt (rounds j (startTerm blank c)) = some row := by
  let initial := initialRow (core c) k
  let last := run (sweep (liftRule δ blank) none) initial n
  let before := (trace (sweep (liftRule δ blank) none) initial n).map (tiles (liftRule δ blank) none)
  let us := writeSites before last
  let vs := us.map Site.current
  let w := initial.length+1
  have cert : siteCheck (liftRule δ blank) initial before last w = true := siteCheck_complete .. 
  obtain ⟨hw,head,tiles,probes⟩ := tableau_tracks_complete _ _ _ _ cert
  obtain ⟨pre,keyEq⟩ := genuine_key (A Q Γ) (core c) k before last vs w head probes
  obtain ⟨age,gate⟩ := (Join.both_iff (A Q Γ) (FiniteCodes.wide _) FiniteCodes.starts FiniteCodes.ends
    [] us vs w hw).mpr probes
  have st : siteTest δ blank halt us = true := (staticRows _ _ _ _).mpr
    ⟨before,last,k,core c,rfl,tiles,hit,head⟩
  have yes := (Static.wordOK_iff (A Q Γ) [] (siteTest δ blank halt) (payload (A Q Γ) us vs w [])).mpr
    ⟨us,vs,w,rfl,hw,st⟩
  change payload (A Q Γ) us vs w [] = _ at keyEq
  rw [keyEq] at gate yes
  exact (first_output_domain _ _ _ _).mpr ⟨pre,age,yes,gate⟩

private theorem forget_sweep (F : Rule C) (blank wall : C) (p : Option (Mark C)) (r : List (Mark C)) :
    (sweep (markedRule F blank wall) p r).map (forget blank wall) =
    sweep F (p.map (forget blank wall)) (r.map (forget blank wall)) := by
  induction r generalizing p with
  | nil => rfl
  | cons c cs ih => simp [sweep,markedRule,forget,List.head?_map,ih]

private theorem forget_run (δ : Table Q Γ) (blank : Γ) (r : List (Mark (Color Q Γ))) (n : Nat) :
    (run (sweep (liftRule δ blank) none) r n).map (erase blank) =
    run (sweep (rule δ) none) (r.map (erase blank)) n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp only [run,ih,forget_sweep,Option.map_none]

private theorem forget_initial (blank : Γ) (c : Cfg Q Γ) (k : Nat) :
    (initialRow (core c) k).map (erase blank) = encode (pad blank c (k+1)) := by
  simp [initialRow,core,encode,pad,erase,forget,List.map_map,Function.comp_def,List.append_assoc,List.replicate_succ]

private theorem final_halt (halt : Q → Bool) (blank : Γ) (r : List (Mark (Color Q Γ))) :
    r.any (haltColor halt ∘ erase blank) = haltSeen halt (r.map (erase blank)) := by
  rw [haltSeen,List.any_map]
  rfl

theorem sound (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (c : Cfg Q Γ) (j : Nat) (row)
    (h : report δ blank halt (rounds j (startTerm blank c)) = some row) :
    ∃ n k, halt (run (advance δ blank) c n).state = true ∧
      row = encode (pad blank (run (advance δ blank) c n) k) := by
  obtain ⟨n,k,done,val⟩ := decode_data δ blank halt c j row h
  rw [final_halt,forget_run,forget_initial] at done
  rw [forget_run,forget_initial] at val
  rcases finite_tracks_infinite δ blank c n (k+1) with ⟨m,ok⟩ | ⟨_,xs,bad⟩
  · rw [ok,halt_encode] at done
    exact ⟨n,m,done,val.symm.trans ok⟩
  · rw [bad,halt_dead] at done; cases done

theorem domain (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (c : Cfg Q Γ) :
    (∃ j row, report δ blank halt (rounds j (startTerm blank c)) = some row) ↔
    ∃ n, halt (run (advance δ blank) c n).state = true := by
  constructor
  · rintro ⟨j,row,hit⟩; obtain ⟨n,_,done,_⟩ := sound δ blank halt c j row hit; exact ⟨_,done⟩
  · rintro ⟨n,done⟩
    apply encode_data δ blank halt c n n
    rw [final_halt,forget_run,forget_initial]
    rcases finite_tracks_infinite δ blank c n (n+1) with ⟨k,h⟩ | ⟨lt,_⟩
    · rw [h,halt_encode]; exact done
    · omega

theorem report_length (δ : Table Q Γ) (blank : Γ) (halt : Q → Bool) (t : Term) (row)
    (h : report δ blank halt t = some row) : row.length ≤ size t := by
  obtain ⟨u,o,ok⟩ := first_sound _ _ _ h
  obtain ⟨w,r,rfl,_,_,out⟩ := (localReport_iff _ _ _ _ _).mp ok
  have bound := OutputStream.output_bound (OutputStream.reader (A Q Γ) (projection blank)) .header w
  change (getRow (Q:=Q) blank w).length ≤ w.length at bound
  rw [out] at bound
  have wl (z : List Bool) : z.length ≤ size (W z) := by
    induction z with
    | nil => simp
    | cons b z ih =>
      change (b::z).length ≤ size (Frames.word Shell.g (b::z))
      rw [Generation.addWord]
      have nz := sizePos (Generation.op b)
      change z.length+1 ≤ size (Generation.op b) + size (W z); omega
  have tagSize : size (W w) ≤ size (tag w ⋆ r) := by simp only [tag,size]; omega
  exact Nat.le_trans bound (Nat.le_trans (wl w) (Nat.le_trans tagSize o.sizeLE))

theorem size_start (blank : Γ) (c : Cfg Q Γ) :
    size (startTerm blank c) ≤ 2*size Shell.g+1+
      3*((c.left.length+1+c.right.length+3)*(A Q Γ).width) := by
  let a := A Q Γ
  have len : (key a (core c)).length = (c.left.length+1+c.right.length+3)*a.width := by
    simp [key,chunks_len,core,Nat.add_mul]; omega
  have w := MachineAlphabet.word_bound (key a (core c))
  change size Shell.g + size (W (key a (core c))) ≤ _
  rw [len] at w
  change _ ≤ 2*size Shell.g+1+3*((c.left.length+1+c.right.length+3)*a.width)
  omega

#print axioms size_start
#print axioms report_regular
#print axioms sound
#print axioms domain
end TwoScans.AnyTape
