module
public import IntegralNormalizationConductorDenominator318
public import OriginalNormalizationConductorSpecialization318
public section
noncomputable section
namespace OriginalNormalizationConductorNonzero318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalizationDifferentValue318 OriginalNormalizationConductorSpecialization318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "B" => SourceOpenRing c t w D
local notation "a" => contacts c t w

local instance sourceDomain : IsDomain B :=
  IntegralDistinctContactOpen318.open_domain R a D.coefficients (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)

/-- A proved nonzero ORIGINAL-point value of the actual normalization
conductor, produced from a whole-order denominator, not a generic density
or dimension argument. Valid even before integral-chart selection. -/
theorem exists_nonzero_value : ∃ y : K c t,y ∈ conductorValues c t w D M ∧ y ≠ 0 := by
  obtain ⟨n,hn⟩ := IntegralNormalizationConductorDenominator318.exists_power
    R a D.coefficients (coefficients_ne_zero c t w D)
  let b : B := algebraMap (Polynomial R) B
    (IntegralNormalizationConductorDenominator318.denominator R a D.coefficients)
  refine ⟨evaluation c t w D M (b^n),⟨b^n,hn,rfl⟩,?_⟩
  have hb : IsUnit b := IntegralNormalizationConductorDenominator318.denominator_isUnit
    R a D.coefficients
  exact ((hb.pow n).map (evaluation c t w D M).toRingHom).ne_zero

lemma conductorValues_ne_bot : conductorValues c t w D M ≠ ⊥ := by
  intro h
  obtain ⟨y,hy,hy0⟩ := exists_nonzero_value c t w D M
  rw [h] at hy
  exact hy0 (Submodule.mem_bot.mp hy)

/-- The actual normalized codifferent value module has a nonzero
original-point value as well, with the same exact inverse different. -/
lemma codifferentValues_ne_bot : codifferentValues c t w D M ≠ ⊥ := by
  obtain ⟨y,hy,hy0⟩ := exists_nonzero_value c t w D M
  have hz : (differentValue c t w D M)⁻¹*y ∈ codifferentValues c t w D M :=
    (mem_iff_inverse c t w D M _).mpr ⟨y,hy,rfl⟩
  intro h
  rw [h] at hz
  exact mul_ne_zero (inv_ne_zero (differentValue_ne c t w D M)) hy0
    (Submodule.mem_bot.mp hz)
end OriginalNormalizationConductorNonzero318
