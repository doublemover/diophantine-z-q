module
public import IntegralClosureLocalizationField318
public section
noncomputable section
namespace IntegralClosureSubmonoidField318
variable (A B L : Type*) [CommRing A] [CommRing B] [CommRing L]
  [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]

/-- Inverting an arbitrary displayed coefficient submonoid inside the same
ambient ring does not enlarge that ring: all its images are already units
through the displayed localized base. -/
theorem ambient_localization (M : Submonoid A) [IsLocalization M B] :
    IsLocalization (Algebra.algebraMapSubmonoid L M) L where
  map_units m := by
    obtain ⟨a, ha, h⟩ := m.property
    change IsUnit (m : L)
    rw [← h, IsScalarTower.algebraMap_apply A B L]
    exact (IsLocalization.map_units B ⟨a, ha⟩).map (algebraMap B L)
  surj z := ⟨⟨z, 1⟩, by simp⟩
  exists_of_eq {x y} h := ⟨1, by simpa using h⟩

/-- Integral closure commutes with the exact coefficient localization,
using the same-element inclusion in the SAME ambient ring. No fraction
field, normality, or finite-generation assumption is added. -/
theorem localization (M : Submonoid A) [IsLocalization M B] :
    letI := IntegralClosureLocalizationField318.closureAlgebra A B L
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) M)
      (integralClosure B L) := by
  letI := IntegralClosureLocalizationField318.closureAlgebra A B L
  letI := IntegralClosureLocalizationField318.closureBaseTower A B L
  letI := IntegralClosureLocalizationField318.closureFieldTower A B L
  letI := ambient_localization A B L M
  exact IsLocalization.integralClosure (S := L) (Rf := B) (Sf := L) M

end IntegralClosureSubmonoidField318
