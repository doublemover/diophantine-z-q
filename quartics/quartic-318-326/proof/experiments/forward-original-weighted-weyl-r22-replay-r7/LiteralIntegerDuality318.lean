module
public import LiteralDualLineIncidence318
public section
noncomputable section
namespace LiteralIntegerDuality318
open TernaryQuadraticLineCover318 LiteralDualLineIncidence318 LiteralTernaryReduction318
set_option maxHeartbeats 2000000

@[expose] def dot (v u : Vector ℤ) : ℤ := v.1*u.1+v.2.1*u.2.1+v.2.2*u.2.2
lemma dot_cast (p : ℕ) [Fact p.Prime] (v u : Vector ℤ) :
    (dot v u:ZMod p)=pairing (TernaryCongruenceLattices318.reduce p v)
      (TernaryCongruenceLattices318.reduce p u) := by
  simp [dot,pairing,TernaryCongruenceLattices318.reduce]

/-- The literal direction annihilates the entire ACTUAL integer local
kernel, not only a chosen representative of its reduced line. -/
lemma annihilates_of_code (p : ℕ) [Fact p.Prime] (κ : ℤ) (t : Option (ZMod p))
    (v u : Vector ℤ) (hu : literalIntegerCode p κ t u=0)
    (hv : pairing (TernaryCongruenceLattices318.reduce p v) (generator (κ:ZMod p) t)=0) :
    (dot v u:ZMod p)=0 := by
  rw [dot_cast]
  cases t with
  | none =>
    change ((u.1:ZMod p),(u.2.2:ZMod p))=(0,0) at hu
    have hx := congrArg Prod.fst hu
    have hw := congrArg Prod.snd hu
    have hz : (v.2.1:ZMod p)=0 := by
      simpa [pairing,generator,TernaryCongruenceLattices318.reduce] using hv
    dsimp [pairing,TernaryCongruenceLattices318.reduce]
    rw [hx,hw,hz]
    ring
  | some s =>
    change ((u.2.1:ZMod p)-(κ:ZMod p)*s^2*(u.1:ZMod p),
      (u.2.2:ZMod p)-s*(u.1:ZMod p))=(0,0) at hu
    have hz := sub_eq_zero.mp (congrArg Prod.fst hu)
    have hw := sub_eq_zero.mp (congrArg Prod.snd hu)
    dsimp [pairing,generator,TernaryCongruenceLattices318.reduce] at hv ⊢
    rw [hz,hw]
    linear_combination (u.1:ZMod p)*hv

lemma generator_in_code (p : ℕ) [Fact p.Prime] (κ : ℤ) (t : Option (ZMod p))
    (u : Vector ℤ) (hu : TernaryCongruenceLattices318.reduce p u=generator (κ:ZMod p) t) :
    literalIntegerCode p κ t u=0 := by
  have hx := congrArg Prod.fst hu
  have hz := congrArg (fun z : Vector (ZMod p) => z.2.1) hu
  have hw := congrArg (fun z : Vector (ZMod p) => z.2.2) hu
  cases t <;> dsimp [generator,TernaryCongruenceLattices318.reduce] at hx hz hw
  · change ((u.1:ZMod p),(u.2.2:ZMod p))=(0,0)
    exact Prod.ext hx hw
  · rename_i s
    change ((u.2.1:ZMod p)-(κ:ZMod p)*s^2*(u.1:ZMod p),
      (u.2.2:ZMod p)-s*(u.1:ZMod p))=(0,0)
    rw [hx,hz,hw]
    simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- CRT constructs ONE actual integer vector reducing to every chosen
literal generator simultaneously; it lies in the original integer lattice. -/
theorem simultaneous_generator (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ u : Vector ℤ, u∈literalLattice p κ t ∧
      ∀ i, TernaryCongruenceLattices318.reduce (p i) u=generator (κ:ZMod (p i)) (t i) := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  obtain ⟨a,ha⟩ := SquarefreeTernaryLatticeCover318.integer_residue_lift p hp hd
    (fun i => (generator (κ:ZMod (p i)) (t i)).1)
  obtain ⟨b,hb⟩ := SquarefreeTernaryLatticeCover318.integer_residue_lift p hp hd
    (fun i => (generator (κ:ZMod (p i)) (t i)).2.1)
  obtain ⟨c,hc⟩ := SquarefreeTernaryLatticeCover318.integer_residue_lift p hp hd
    (fun i => (generator (κ:ZMod (p i)) (t i)).2.2)
  have hu (i : ι) : TernaryCongruenceLattices318.reduce (p i) (a,b,c)=
      generator (κ:ZMod (p i)) (t i) := Prod.ext (ha i) (Prod.ext (hb i) (hc i))
  refine ⟨(a,b,c),?_,hu⟩
  change literalGlobalCode p κ t (a,b,c)=0
  funext i
  exact generator_in_code (p i) κ (t i) (a,b,c) (hu i)

/-- Exact dual congruence of the ACTUAL integer sublattice. Membership of
v/q in its Euclidean dual will require a separate real-lattice embedding;
no successive-minimum/transference theorem is assumed here. -/
theorem original_duality_iff (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (v : Vector ℤ) :
    (∀ u : Vector ℤ, u∈literalLattice p κ t → (FixedSquarefreeCRT318.modulus p:ℤ)∣dot v u) ↔
    ∀ i, pairing (TernaryCongruenceLattices318.reduce (p i) v)
      (generator (κ:ZMod (p i)) (t i))=0 := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  constructor
  · intro h i
    obtain ⟨u,hu,hred⟩ := simultaneous_generator p hp hd κ t
    have hdiv := (SquarefreeTernaryLatticeCover318.product_divisor_iff p hp hd (dot v u)).mp (h u hu) i
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (dot v u) (p i)).mpr hdiv
    rw [dot_cast,hred i] at hz
    exact hz
  · intro h u hu
    apply (SquarefreeTernaryLatticeCover318.product_divisor_iff p hp hd (dot v u)).mpr
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (dot v u) (p i)).mp
    apply annihilates_of_code (p i) κ (t i) v u _ (h i)
    change literalGlobalCode p κ t u=0 at hu
    exact congrFun hu i

end LiteralIntegerDuality318
