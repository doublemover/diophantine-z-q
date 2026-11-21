module
public import ActualMulGlobalEtale318
public import ActualEtaleLocallyQuasiFinite318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import all WeierstrassGluing318
public section
noncomputable section

namespace ActualMulKernelFiniteEtale318
open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318
open ActualMulGlobalEtale318

variable (n m : ℕ)
local notation "R₀" => OpenJModel318.Base n

/-- The actual multiplication has the same proper structure map on
both source and target, not a separately chosen compactification. -/
theorem mul_proper : IsProper (mulMap n m) := by
  letI : IsProper (projection n) := CubicClosedImmersion318.literal_proper n
  haveI : IsProper (mulMap n m ≫ projection n) := by rw [mul_over]; infer_instance
  exact IsProper.of_comp (mulMap n m) (projection n)

theorem mul_finite (hm : IsUnit (m : R₀)) : IsFinite (mulMap n m) := by
  haveI : Etale (mulMap n m) := mul_etale n m hm
  haveI : IsProper (mulMap n m) := mul_proper n m
  haveI : LocallyQuasiFinite (mulMap n m) :=
    ActualEtaleLocallyQuasiFinite318.locallyQuasiFinite (mulMap n m)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (mulMap n m)

/-- The true [m]-kernel is the actual pullback along the literal zero
section. Both facts are on that very projection, with no degree claim. -/
theorem kernel_finite_etale (hm : IsUnit (m : R₀)) :
    IsFinite (kernelProjection n m) ∧ Etale (kernelProjection n m) := by
  haveI : IsFinite (mulMap n m) := mul_finite n m hm
  haveI : Etale (mulMap n m) := mul_etale n m hm
  exact ⟨inferInstance, inferInstance⟩

theorem level_kernel_finite_etale (N : ℕ) :
    IsFinite (kernelProjection N N) ∧ Etale (kernelProjection N N) :=
  kernel_finite_etale N N (OpenJModel318.base_units N).2.2.1

end ActualMulKernelFiniteEtale318
