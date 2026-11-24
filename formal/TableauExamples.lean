import TableauEndToEnd

/- Two independent concrete source computations, instantiated at the final
ground S theorem. The proof for echo covers every binary input. No large S
tree is materialized to establish the unbounded existence and absence claims. -/
namespace TwoScans.Tableau.Examples
open Certificate OneTape MachineAlphabet Term Frames
abbrev Sym := Symbol Unit

def echo : Table Bool Sym := fun _ c => match c with
  | .start => ⟨false,.start,.right⟩
  | .bit b => ⟨false,.outputBit b,.right⟩
  | _ => ⟨true,c,.stay⟩

def reading (seen : List Bool) : List Bool → Cfg Bool Sym
  | [] => ⟨seen.map .outputBit ++ [.start], false, .inputEnd, []⟩
  | b::bs => ⟨seen.map .outputBit ++ [.start], false, .bit b, bs.map .bit ++ [.inputEnd]⟩
def finish (seen : List Bool) : Cfg Bool Sym :=
  ⟨seen.map .outputBit ++ [.start], true, .inputEnd, []⟩
abbrev echoStep := advance (stopped echo id) .blank

private theorem start_read (x : List Bool) : echoStep (initial false x) = reading [] x := by
  cases x <;> rfl

private theorem consumes (seen rest : List Bool) :
    run echoStep (reading seen rest) (rest.length+1) = finish (rest.reverse ++ seen) := by
  induction rest generalizing seen with
  | nil => rfl
  | cons b bs ih =>
    have h : echoStep (reading seen (b::bs)) = reading (b::seen) bs := by cases bs <;> rfl
    change run echoStep (echoStep (reading seen (b::bs))) (bs.length+1) = _
    rw [h,ih]
    simp [List.append_assoc]

theorem echo_source (x : List Bool) : Computes echo id false x x := by
  refine ⟨x.length+2,?_⟩
  have h : run echoStep (initial false x) (x.length+2) = finish x.reverse := by
    change run echoStep (echoStep (initial false x)) (x.length+1) = _
    rw [start_read,consumes,List.append_nil]
  change id (run echoStep (initial false x) (x.length+2)).state = true ∧
    output mark (encode (run echoStep (initial false x) (x.length+2))) = x
  rw [h]
  simp [output,encode,finish,mark,List.filterMap_map,Function.comp_def]

/-- In particular [] produces some []; a divergent tree produces none at
every round. This theorem also excludes any incorrect output on any input. -/
theorem echo_ground (x y : List Bool) :
    (∃ n, (machineTests echo id false).report (rounds n (encodeInput (Z:=Unit) false x)) = some y) ↔ x = y := by
  rw [machine_output_iff]
  exact ⟨computes_unique _ _ _ (echo_source x),fun e => e ▸ echo_source x⟩

def loop : Table Bool Sym := fun q c => ⟨q,c,.stay⟩

private theorem never_halts (x y : List Bool) : ¬ Computes loop id false x y := by
  rintro ⟨n,h,o⟩
  have e : run (advance (stopped loop id) .blank) (initial (Z:=Unit) false x) n = initial false x := by
    clear h o
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  rw [e] at h
  contradiction

theorem divergent_ground (x : List Bool) (n : Nat) :
    (machineTests loop id false).report (rounds n (encodeInput (Z:=Unit) false x)) = none := by
  cases e : (machineTests loop id false).report (rounds n (encodeInput (Z:=Unit) false x)) with
  | none => rfl
  | some y => exact False.elim (never_halts x y (every_output loop id false x y n e))

#guard (run echoStep (initial false [true,false]) 4).state == true
#guard output mark (encode (run echoStep (initial false [true,false]) 4)) == [true,false]
#guard output mark (encode (run echoStep (initial false []) 2)) == []
#print axioms echo_ground
#print axioms divergent_ground
end TwoScans.Tableau.Examples
