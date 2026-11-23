module
public import Init.Data.List.Lemmas
public section

/-! Lean core only. No Mathlib, projector dependency, or opaque signed
witness choice. List.any is the finite OR; a list of distinct row keys
models the original Finset. The control fixtures are closed kernel decisions. -/
namespace LinearA4WeightedReadbackCoreSmoke318

variable {X ι T W : Type} {R : X → Type}

/-- The two flags are read from the same witness of the same row. -/
def event (minus plus : (x : X) → R x → ι → Bool) (x : X) (r : R x) (s : ι × ι) :
    Bool :=
  minus x r s.1 && plus x r s.2

/-- Original existential order: first find one acceptable signed lift,
then select a genuinely ordered pair of tested slots. -/
def witnessFirst (witnesses : (x : X) → List (R x)) (pairs : List (ι × ι))
    (minus plus : (x : X) → R x → ι → Bool) (x : X) : Bool :=
  (witnesses x).any fun r => pairs.any (event minus plus x r)

/-- Union of lists of keys recognized by encoded, fixed-companion shapes.
The geometric companion is allowed to be invisible to `tested`. -/
def shapeFirst (witnesses : (x : X) → List (R x)) (pairs : List (ι × ι))
    (minus plus : (x : X) → R x → ι → Bool)
    (encode : ι × ι → T) (tested : T → ι × ι) (x : X) : Bool :=
  pairs.any fun s => (witnesses x).any fun r => event minus plus x r (tested (encode s))

/-- For the native case, `recover` is precisely `tested_select (fixedMate C)`.
This step swaps the pair and witness quantifiers but never splits the two signs. -/
theorem same_decision (witnesses : (x : X) → List (R x)) (pairs : List (ι × ι))
    (minus plus : (x : X) → R x → ι → Bool)
    (encode : ι × ι → T) (tested : T → ι × ι)
    (recover : ∀ s, tested (encode s) = s) (x : X) :
    witnessFirst witnesses pairs minus plus x =
      shapeFirst witnesses pairs minus plus encode tested x := by
  apply Bool.eq_iff_iff.mpr
  change (witnesses x).any (fun r => pairs.any (event minus plus x r)) = true ↔
    pairs.any (fun s => (witnesses x).any (fun r => event minus plus x r (tested (encode s)))) = true
  simp only [List.any_eq_true, recover]
  constructor
  · intro h
    obtain ⟨r,hr,s,hs,ev⟩ := h
    exact ⟨s,hs,r,hr,ev⟩
  · intro h
    obtain ⟨s,hs,r,hr,ev⟩ := h
    exact ⟨r,hr,s,hs,ev⟩

/-- The filtered original key list is unchanged; arbitrary weights are
mapped *after* the union. This is not an additive formula over the shapes. -/
theorem same_weighted_keys (rows : List X) (witnesses : (x : X) → List (R x))
    (pairs : List (ι × ι)) (minus plus : (x : X) → R x → ι → Bool)
    (encode : ι × ι → T) (tested : T → ι × ι)
    (recover : ∀ s, tested (encode s) = s) (weight : X → W) :
    (rows.filter (witnessFirst witnesses pairs minus plus)).map weight =
      (rows.filter (shapeFirst witnesses pairs minus plus encode tested)).map weight := by
  apply congrArg (List.map weight)
  exact List.filter_congr (fun x _ => same_decision witnesses pairs minus plus encode tested recover x)

def oneSlot : List (Unit × Unit) := [((),())]
def lifts (_ : Unit) : List Bool := [false,true]
def negRead (_ : Unit) (r : Bool) (_ : Unit) : Bool := !r
def posRead (_ : Unit) (r : Bool) (_ : Unit) : Bool := r

/-- Negative control: independent lifts make both translated residue predicates
true, but no single lift makes the collision true. -/
theorem split_witness_false_positive :
    (lifts ()).any (fun r => negRead () r ()) = true ∧
    (lifts ()).any (fun r => posRead () r ()) = true ∧
    witnessFirst lifts oneSlot negRead posRead () = false := by decide

def twoDiagonals : List (Bool × Bool) := [(false,false),(true,true)]
def oneLift (_ : Unit) : List Unit := [()]
def always (_ : Unit) (_ : Unit) (_ : Bool) : Bool := true

def encodeBool (s : Bool × Bool) : Bool × Bool × Bool :=
  (s.1, !s.1, s.1 == s.2)

def testedBool (t : Bool × Bool × Bool) : Bool × Bool :=
  (t.1, if t.2.2 then t.1 else t.2.1)

theorem tested_encode_bool (s : Bool × Bool) : testedBool (encodeBool s) = s := by
  cases s with
  | mk i j => cases i <;> cases j <;> decide

/-- Negative control: two distinct shapes hit one key. Summing their
weights would count it twice; selecting from the whole union counts it once. -/
theorem additivity_false_positive :
    (([()] : List Unit).filter (shapeFirst oneLift twoDiagonals always always encodeBool testedBool) |>.map
      (fun _ => (7 : Nat)) |>.sum) = 7 ∧
    (twoDiagonals.map (fun s =>
      if witnessFirst oneLift [s] always always () then (7 : Nat) else 0) |>.sum) = 14 := by decide

end LinearA4WeightedReadbackCoreSmoke318
