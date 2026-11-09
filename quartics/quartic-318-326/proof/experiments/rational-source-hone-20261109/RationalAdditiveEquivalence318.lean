module
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.LinearAlgebra.Basis.Defs
public section
noncomputable section
namespace RationalAdditiveEquivalence318
@[expose] def equivalence {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℚ M] [Module ℚ N] (e : M ≃+ N) : M ≃ₗ[ℚ] N :=
  { e with map_smul' := map_rat_smul e }
end RationalAdditiveEquivalence318
