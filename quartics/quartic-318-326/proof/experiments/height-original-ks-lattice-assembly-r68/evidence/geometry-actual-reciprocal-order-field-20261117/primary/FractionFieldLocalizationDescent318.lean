module
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace FractionFieldLocalizationDescent318
variable {R S F:Type*} [CommRing R] [CommRing S] [Field F]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  [FaithfulSMul R F]
/-- Descend an actual fraction-field identification through a specified localization. -/
theorem of_localization (M:Submonoid R) [IsLocalization M S] [IsFractionRing S F] :
    IsFractionRing R F := by
  let N:=IsLocalization.localizationLocalizationSubmodule M (nonZeroDivisors S)
  letI:IsLocalization N F:=IsLocalization.localization_localization_isLocalization M (nonZeroDivisors S) F
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨a,b⟩,h⟩:=IsLocalization.surj N z
  exact ⟨a,b,(eq_div_iff (IsLocalization.map_units F b).ne_zero).mpr h⟩
end FractionFieldLocalizationDescent318
