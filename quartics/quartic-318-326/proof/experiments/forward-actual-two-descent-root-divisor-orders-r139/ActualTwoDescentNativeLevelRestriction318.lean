module
public import ActualTwoDescentNativeScalarContinuity318
public section
noncomputable section
namespace ActualTwoDescentNativeLevelRestriction318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentAdditivePrimaryLevels318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentPrimaryPadicScalar318 ActualTwoDescentHigherCohomologyDirectedMaps318

/-- The actual subgroup killed by 2^k, rather than an abstract cyclic model. -/
def DiscreteSelmerLevel (n : ℚ) (hn : n ≠ 0) (k : ℕ) :=
  Multiplicative (additivePowerLevel (actualPrimarySelmer n hn) k)
instance (n : ℚ) (hn : n ≠ 0) (k : ℕ) : CommGroup (DiscreteSelmerLevel n hn k) :=
  inferInstanceAs (CommGroup (Multiplicative (additivePowerLevel (actualPrimarySelmer n hn) k)))
instance (n : ℚ) (hn : n ≠ 0) (k : ℕ) : TopologicalSpace (DiscreteSelmerLevel n hn k) := ⊥
instance (n : ℚ) (hn : n ≠ 0) (k : ℕ) : DiscreteTopology (DiscreteSelmerLevel n hn k) := ⟨rfl⟩
instance (n : ℚ) (hn : n ≠ 0) (k : ℕ) : IsTopologicalGroup (DiscreteSelmerLevel n hn k) := inferInstance

abbrev NativeLevelDual (n : ℚ) (hn : n ≠ 0) (k : ℕ) :=
  PontryaginDual (DiscreteSelmerLevel n hn k)

def nativeLevelInclusion (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    DiscreteSelmerLevel n hn k →ₜ* DiscreteSelmer n hn where
  toFun x := Multiplicative.ofAdd x.toAdd.val
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

def nativeLevelTransition (n : ℚ) (hn : n ≠ 0) (i j : ℕ) (hij : i ≤ j) :
    DiscreteSelmerLevel n hn i →ₜ* DiscreteSelmerLevel n hn j where
  toFun x := Multiplicative.ofAdd ⟨x.toAdd.val, actual_nsmul_power_mono hij x.toAdd.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

/-- Continuous restriction between the original native compact duals. -/
def nativeLevelRestriction (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    ActualPontryagin n hn →ₜ* NativeLevelDual n hn k :=
  PontryaginDual.map (nativeLevelInclusion n hn k)

def nativeLevelDualTransition (n : ℚ) (hn : n ≠ 0) (i j : ℕ) (hij : i ≤ j) :
    NativeLevelDual n hn j →ₜ* NativeLevelDual n hn i :=
  PontryaginDual.map (nativeLevelTransition n hn i j hij)

lemma actual_native_restriction_compatible (n : ℚ) (hn : n ≠ 0)
    (i j : ℕ) (hij : i ≤ j) (f : ActualPontryagin n hn) :
    nativeLevelDualTransition n hn i j hij (nativeLevelRestriction n hn j f) =
      nativeLevelRestriction n hn i f := by
  apply PontryaginDual.ext
  intro x
  rfl

/-- Every actual Selmer element belongs to some finite-exponent level.
Thus equality on ALL these restrictions detects the original character. -/
theorem actual_native_restrictions_injective (n : ℚ) (hn : n ≠ 0)
    (f g : ActualPontryagin n hn)
    (h : ∀ k, nativeLevelRestriction n hn k f = nativeLevelRestriction n hn k g) : f=g := by
  apply PontryaginDual.ext
  intro x
  obtain ⟨k,hk⟩ := actual_selmer_primary n hn x.toAdd
  exact congrArg (fun v : NativeLevelDual n hn k =>
    v (Multiplicative.ofAdd ⟨x.toAdd,hk⟩)) (h k)

def nativeLevelAnnihilator (n : ℚ) (hn : n ≠ 0) (k : ℕ) : Subgroup (ActualPontryagin n hn) :=
  (nativeLevelRestriction n hn k).toMonoidHom.ker

lemma actual_native_annihilator_closed (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    IsClosed (nativeLevelAnnihilator n hn k : Set (ActualPontryagin n hn)) := by
  exact isClosed_singleton.preimage (nativeLevelRestriction n hn k).continuous

lemma actual_native_annihilator_antitone (n : ℚ) (hn : n ≠ 0)
    (i j : ℕ) (hij : i ≤ j) :
    nativeLevelAnnihilator n hn j ≤ nativeLevelAnnihilator n hn i := by
  intro f hf
  change nativeLevelRestriction n hn i f=1
  rw [←actual_native_restriction_compatible n hn i j hij f]
  change nativeLevelRestriction n hn j f=1 at hf
  rw [hf,map_one]

lemma actual_native_all_annihilators (n : ℚ) (hn : n ≠ 0)
    (f : ActualPontryagin n hn) :
    (∀ k, f ∈ nativeLevelAnnihilator n hn k) ↔ f=1 := by
  constructor
  · intro h
    apply actual_native_restrictions_injective n hn f 1
    intro k
    exact (h k).trans (map_one (nativeLevelRestriction n hn k)).symm
  · rintro rfl k
    exact (nativeLevelAnnihilator n hn k).one_mem

end ActualTwoDescentNativeLevelRestriction318
