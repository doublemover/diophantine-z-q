module
public import JLineAtlas318
public section
noncomputable section
namespace IntegralJLineOverlapOpen318
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type*) [CommRing R]

/-- Full standard-chart intersection over an arbitrary coefficient ring. -/
theorem zero_one :
    JLineAtlas318.chart R 0 ⁻¹ᵁ (JLineAtlas318.chart R 1 ''ᵁ ⊤)=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial R) := by
  rw [Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading R)
    (isHomogeneous_X R (0:Fin 2)) (by omega)
    (isHomogeneous_X R (1:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv R 0)
    (Away.isLocalizationElem (isHomogeneous_X R (0:Fin 2))
      (isHomogeneous_X R (1:Fin 2))))=_
  have h : Away.isLocalizationElem (isHomogeneous_X R (0:Fin 2))
      (isHomogeneous_X R (1:Fin 2))=(JLineAtlas318.chartEquiv R 0).symm Polynomial.X := by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]

/-- Full standard-chart intersection over an arbitrary coefficient ring. -/
theorem one_zero :
    JLineAtlas318.chart R 1 ⁻¹ᵁ (JLineAtlas318.chart R 0 ''ᵁ ⊤)=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial R) := by
  rw [Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading R)
    (isHomogeneous_X R (1:Fin 2)) (by omega)
    (isHomogeneous_X R (0:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv R 1)
    (Away.isLocalizationElem (isHomogeneous_X R (1:Fin 2))
      (isHomogeneous_X R (0:Fin 2))))=_
  have h : Away.isLocalizationElem (isHomogeneous_X R (1:Fin 2))
      (isHomogeneous_X R (0:Fin 2))=(JLineAtlas318.chartEquiv R 1).symm Polynomial.X := by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]
end IntegralJLineOverlapOpen318
