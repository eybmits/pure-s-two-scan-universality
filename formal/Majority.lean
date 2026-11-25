import SerialOutput

/-! Every detection along the fixed one-contraction schedule is sound.
Two of the three copies are always at parallel round boundaries. -/
namespace TwoScans.Majority
open Term Frames SerialTableau SerialReadout Automata

def triple (a b c : Term) := pack a (pack b c)

def combine {Y : Type} [DecidableEq Y] (a b c : Option Y) : Option Y :=
  match a,b,c with
  | some x, some y, some z => some (if x = y then x else z)
  | _,_,_ => none

def read {Y : Type} [DecidableEq Y] (D : Term → Option Y) : Term → Option Y
  | .app (.app .s a) (.app (.app .s b) c) => combine (D a) (D b) (D c)
  | _ => none

theorem read_triple {Y} [DecidableEq Y] (D : Term → Option Y) (a b c) :
    read D (triple a b c) = combine (D a) (D b) (D c) := rfl

private theorem in_domain {Y} [DecidableEq Y] {D : Term → Option Y} {t} :
    (∃ y, read D t = some y) ↔
    ∃ a b c, t = triple a b c ∧ (∃ x, D a = some x) ∧
      (∃ x, D b = some x) ∧ (∃ x, D c = some x) := by
  constructor
  · rintro ⟨y,h⟩
    unfold read at h
    split at h
    · rename_i a b c
      refine ⟨a,b,c,rfl,?_⟩
      cases aa : D a <;> cases bb : D b <;> cases cc : D c <;> simp_all [combine]
    · cases h
  · rintro ⟨a,b,c,rfl,⟨x,hx⟩,⟨y,hy⟩,⟨z,hz⟩⟩
    simp [read_triple,combine,hx,hy,hz]

theorem regular_domain {Y} [DecidableEq Y] (D : Term → Option Y)
    (h : Regular (fun t => ∃ y, D t = some y)) :
    Regular (fun t => ∃ y, read D t = some y) := by
  have left := regular_app regular_leaf h
  obtain ⟨Q,fs,F,p,test⟩ := regular_app left (regular_app left h)
  refine ⟨Q,fs,F,p,fun t => ?_⟩
  rw [test]
  change _ ↔ (∃ y, read D t = some y)
  rw [in_domain]
  constructor
  · rintro ⟨_,_,rfl,⟨_,a,rfl,rfl,ha⟩,⟨_,c,rfl,⟨_,b,rfl,rfl,hb⟩,hc⟩⟩
    exact ⟨a,b,c,rfl,ha,hb,hc⟩
  · rintro ⟨a,b,c,rfl,ha,hb,hc⟩
    exact ⟨_,_,rfl,⟨_,a,rfl,rfl,ha⟩,⟨_,c,rfl,⟨_,b,rfl,rfl,hb⟩,hc⟩⟩

private theorem sweep_cases (a z) (seen : z ∈ sweep (triple a a a)) :
    (∃ u, z = triple u a a) ∨ (∃ u, z = triple (parallel a) u a) ∨
    (∃ u, z = triple (parallel a) (parallel a) u) := by
  simp only [triple,sweep_pack,List.mem_append,List.mem_map] at seen
  rcases seen with ⟨u,_,rfl⟩ | ⟨v,(⟨u,_,rfl⟩ | ⟨u,_,rfl⟩),rfl⟩
  · exact .inl ⟨u,rfl⟩
  · exact .inr (.inl ⟨u,rfl⟩)
  · exact .inr (.inr ⟨u,rfl⟩)

private theorem combine_sound {Y} [DecidableEq Y] (P : Y → Prop)
    (unique : ∀ {u v}, P u → P v → u = v) (a b c : Option Y)
    (stable : let good := fun o : Option Y => ∀ v, o = some v → P v
              (good a ∧ good b) ∨ (good a ∧ good c) ∨ (good b ∧ good c))
    {v} (out : combine a b c = some v) : P v := by
  cases a with | none => cases out | some x =>
  cases b with | none => cases out | some y =>
  cases c with | none => cases out | some z =>
  simp only [Option.some.injEq,forall_eq'] at stable
  simp only [combine,Option.some.injEq] at out
  subst v
  rcases stable with ⟨hx,hy⟩ | ⟨hx,hz⟩ | ⟨hy,hz⟩
  · simpa [unique hx hy] using hy
  · split <;> assumption
  · split
    · rename_i eq; exact eq ▸ hy
    · exact hz

theorem every_hit {Y} [DecidableEq Y] (D : Term → Option Y) (e : Term)
    (P : Y → Prop) (unique : ∀ {u v}, P u → P v → u = v)
    (parallelSound : ∀ n y, D (rounds n e) = some y → P y) (n : Nat) (t : Term)
    (atState : t ∈ states (triple e e e) n) {y} (hit : read D t = some y) : P y := by
  induction n with
  | zero =>
    have eq : t = triple e e e := by simpa [states,post] using atState
    subst t
    exact combine_sound P unique _ _ _ (Or.inl ⟨parallelSound 0,parallelSound 0⟩) hit
  | succ n ih =>
    have boundary : rounds n (triple e e e) = triple (rounds n e) (rounds n e) (rounds n e) := by
      simp [triple,rounds_pack]
    have splitAt : t ∈ states (triple e e e) n ∨ t ∈ sweep (triple (rounds n e) (rounds n e) (rounds n e)) := by
      simpa [states,post,List.mem_cons,List.mem_append,boundary,or_assoc] using atState
    rcases splitAt with prev | active
    · exact ih prev
    · have next : parallel (rounds n e) = rounds (n+1) e := by
        rw [rounds_add n 1,parallel_agrees]; rfl
      rcases sweep_cases _ _ active with ⟨u,rfl⟩ | ⟨u,rfl⟩ | ⟨u,rfl⟩
      · exact combine_sound P unique _ _ _ (.inr (.inr ⟨parallelSound n,parallelSound n⟩)) hit
      · rw [next] at hit
        exact combine_sound P unique _ _ _ (.inr (.inl ⟨parallelSound (n+1),parallelSound n⟩)) hit
      · rw [next] at hit
        exact combine_sound P unique _ _ _ (.inl ⟨parallelSound (n+1),parallelSound (n+1)⟩) hit

theorem universal_strings :
    ∃ (E : List Bool → List Bool → Term) (D : Term → Option (List Bool)) (a b : Nat),
      Regular (fun t => ∃ y, D t = some y) ∧
      (∀ p x, size (E p x) ≤ a + b*(p.length+x.length)) ∧
      ∀ f : List Bool →. List Bool, Partrec f → ∃ p : List Bool, ∀ x y,
        (∃ n t, t ∈ states (E p x) n ∧ D t = some y) ↔ y ∈ f x := by
  obtain ⟨E,D,a,b,reg,cap,works⟩ := Prize.universal_strings
  refine ⟨fun p x => triple (E p x) (E p x) (E p x),read D,2+3*a,3*b,regular_domain D reg,?_,?_⟩
  · intro p x
    have := cap p x
    simp only [triple,pack,size,Nat.mul_assoc]
    omega
  · intro f hf
    obtain ⟨p,graph⟩ := works f hf
    refine ⟨p,fun x y => ?_⟩
    constructor
    · rintro ⟨n,t,atState,hit⟩
      exact every_hit D (E p x) (· ∈ f x) Part.mem_unique
        (fun j v h => (graph x v).mp ⟨j,h⟩) n t atState hit
    · intro member
      obtain ⟨n,hit⟩ := (graph x y).mpr member
      refine ⟨n,_,end_mem _ n,?_⟩
      simp only [triple,rounds_pack]
      change combine (D (rounds n (E p x))) (D (rounds n (E p x))) (D (rounds n (E p x))) = some y
      simp [hit,combine]

#print axioms regular_domain
#print axioms every_hit
#print axioms universal_strings
end TwoScans.Majority
