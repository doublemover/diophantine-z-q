module
public import ActualTwoDescentPontryaginFreeRankOne318
public section
noncomputable section
namespace ActualTwoDescentNativeScalarContinuity318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentPontryaginPadicModule318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The independently defined actual Selmer scalar is a continuous map on
its actual discrete topology. No topology is transported from Z_2. -/
def discreteSelmerScalar (n : ℚ) (hn : n ≠ 0) (a : ℤ_[2]) :
    DiscreteSelmer n hn →ₜ* DiscreteSelmer n hn where
  toFun x := Multiplicative.ofAdd (actualSelmerPadicEnd n hn a x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [map_add]
  continuous_toFun := continuous_of_discreteTopology

/-- Functorial native Pontryagin precomposition, with its compact-open
continuity supplied by the library, is exactly the specified scalar. -/
def nativeScalarContinuousHom (n : ℚ) (hn : n ≠ 0) (a : ℤ_[2]) :
    ActualPontryagin n hn →ₜ* ActualPontryagin n hn :=
  PontryaginDual.map (discreteSelmerScalar n hn a)

lemma actual_native_scalar_identification (n : ℚ) (hn : n ≠ 0)
    (a : ℤ_[2]) (f : ActualPontryagin n hn) :
    nativeScalarContinuousHom n hn a f = nativeDualScalar n hn a f := by
  apply PontryaginDual.ext
  intro x
  rfl

lemma actual_native_scalar_continuous (n : ℚ) (hn : n ≠ 0) (a : ℤ_[2]) :
    Continuous (nativeDualScalar n hn a) := by
  have h : nativeDualScalar n hn a = nativeScalarContinuousHom n hn a := by
    funext f
    exact (actual_native_scalar_identification n hn a f).symm
  rw [h]
  exact (nativeScalarContinuousHom n hn a).continuous

end ActualTwoDescentNativeScalarContinuity318
