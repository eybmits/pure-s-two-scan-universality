import ObserverClass
import ShellStatic
import PayloadBits

namespace TwoScans.OutputStream
open WordBlocks PayloadBits TrackLayout Tableau Automata Observer

/-- Mealy machine with at most one output bit per input bit. -/
structure Reader (Q Y : Type) where
  transition : Q → Bool → Q × Option Y

def transduce (r : Reader Q Y) : Q → List Bool → List Y
  | _,[] => []
  | q,b::bs =>
    let (q',out) := r.transition q b
    out.elim (transduce r q' bs) (fun d => d::transduce r q' bs)

theorem output_bound (r : Reader Q Y) (q) (w) : (transduce r q w).length ≤ w.length := by
  induction w generalizing q with
  | nil => exact Nat.le_refl _
  | cons b w ih =>
    simp only [transduce]
    cases e : r.transition q b with
    | mk q' out => cases out <;> simp_all [Option.elim] <;> exact Nat.le_succ_of_le (ih _)

inductive Mode (s : Nat) where
  | header | body (pre : Short s) | done
instance (s : Nat) : FinStates (Mode s) where
  enum := [.header,.done] ++ FinStates.enum.map .body
  covers x := by cases x with
                 | body t => simp [FinStates.covers t]
                 | _ => simp

variable {R C : Type} [FinStates (Label R C)]
def reader (A : Alphabet (Label R C)) (emit : R → Option Y) : Reader (Mode A.width) Y where
  transition q b := match q with
    | .header => (if b then .header else .body (blank _),none)
    | .done => (.done,none)
    | .body pre =>
      let xs := pre.1 ++ [b]
      if h : xs.length < A.width then (.body ⟨xs,by omega⟩,none)
      else match decodeBits A xs with
        | some .ue => (.done,none)
        | some (.site a) => (.body (blank _),emit a)
        | _ => (.body (blank _),none)

private theorem done (A : Alphabet (Label R C)) (emit : R → Option Y) (w) :
    transduce (reader A emit) .done w = [] := by induction w <;> simp_all [transduce,reader,Option.elim]

private theorem header (A : Alphabet (Label R C)) (emit : R → Option Y) (n) (r : List Bool) :
    transduce (reader A emit) .header (List.replicate n true ++ false::r) =
    transduce (reader A emit) (.body (blank _)) r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,transduce,reader] using ih

private def finish (A : Alphabet (Label R C)) (emit : R → Option Y) (a : Label R C) (tail : List Bool) : List Y :=
  match a with
  | .ue => []
  | .site r => (emit r).elim (transduce (reader A emit) (.body (blank _)) tail)
      (fun b => b :: transduce (reader A emit) (.body (blank _)) tail)
  | _ => transduce (reader A emit) (.body (blank _)) tail

private theorem buffer (A : Alphabet (Label R C)) (emit : R → Option Y) (a : Label R C)
    (pre : Short A.width) (digits tail : List Bool) (b : Bool)
    (h : pre.val ++ digits ++ [b] = A.code a) :
    transduce (reader A emit) (.body pre) (digits ++ b::tail) = finish A emit a tail := by
  induction digits generalizing pre with
  | nil =>
    have he : pre.val ++ [b] = A.code a := by simpa using h
    have hl : ¬(pre.val ++ [b]).length < A.width := by rw [he,A.length]; omega
    have step : (reader A emit).transition (.body pre) b = match a with
        | .ue => (.done,none)
        | .site r => (.body (blank _),emit r)
        | _ => (.body (blank _),none) := by
      simp only [reader,he,A.length,Nat.lt_irrefl,dite_false,decodeBits_code]
      cases a <;> rfl
    cases a <;> simp only [List.nil_append,transduce,step,finish,Option.elim,done]
  | cons x xs ih =>
    have ht := congrArg List.length h
    simp only [List.length_append,List.length_cons,List.length_nil,A.length] at ht
    have small : (pre.val ++ [x]).length < A.width := by simp; omega
    have eq : (pre.val ++ [x]) ++ xs ++ [b] = A.code a := by simpa [List.append_assoc] using h
    simpa only [List.cons_append,transduce,reader,dite_eq_left small,Option.elim] using
      ih ⟨pre.val ++ [x],by omega⟩ eq

private theorem block (A : Alphabet (Label R C)) (ends : ∀ a, ∃ bs, A.code a = bs ++ [true])
    (emit : R → Option Y) (a : Label R C) (tail : List Bool) :
    transduce (reader A emit) (.body (blank _)) (A.code a ++ tail) = finish A emit a tail := by
  obtain ⟨bs,eq⟩ := ends a
  rw [eq,List.append_assoc]
  exact buffer A emit a (blank _) bs tail true (by simp [blank,eq])

theorem on_payload (A : Alphabet (Label R C)) (ends : ∀ a, ∃ ds, A.code a = ds ++ [true])
    (emit : R → Option Y) (us : List R) (vs : List C) (w : Nat) (foot : List Bool) :
    transduce (reader A emit) .header (payload A us vs w foot) = us.filterMap emit := by
  let rest := chunks A (.ve :: vs.reverse.map .color ++ [.vb]) ++ foot
  have cells (xs : List R) : transduce (reader A emit) (.body (blank _))
      (chunks A (xs.map .site ++ [.ue]) ++ rest) = xs.filterMap emit := by
    induction xs with
    | nil => simp only [List.map_nil,List.nil_append,chunks,List.flatMap_cons,List.flatMap_nil,List.append_nil]
             rw [block A ends]; rfl
    | cons x xs ih =>
      change transduce _ _ ((A.code (.site x) ++ chunks A (xs.map .site ++ [.ue])) ++ rest) = _
      rw [List.append_assoc,block A ends]
      cases hv : emit x <;> simp [finish,hv,ih,Option.elim]
  have shape : payload A us vs w foot =
      List.replicate (w*A.width) true ++ false::(A.code .ub ++ (chunks A (us.map .site ++ [.ue]) ++ rest)) := by
    simp [payload,bodyLabels,chunks,rest,List.append_assoc]
  rw [shape,header,block A ends]
  exact cells us

end TwoScans.OutputStream
#print axioms TwoScans.OutputStream.on_payload
