module
public import NormalizedWholeOpenRanges318
public section
noncomputable section
namespace NormalizedProjectiveChartIntersection318
open Polynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R]
theorem chart_one_preimage_zero :
    JLineAtlas318.chart R 1 ⁻¹ᵁ (JLineAtlas318.chart R 0 ''ᵁ ⊤)=
      PrimeSpectrum.basicOpen (X:R[X]) := by
  rw [Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading R)
    (MvPolynomial.isHomogeneous_X R (1:Fin 2)) (by omega)
    (MvPolynomial.isHomogeneous_X R (0:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv R 1)
    (HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (1:Fin 2))
      (MvPolynomial.isHomogeneous_X R (0:Fin 2))))=_
  have h : HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (1:Fin 2))
      (MvPolynomial.isHomogeneous_X R (0:Fin 2))=
      (JLineAtlas318.chartEquiv R 1).symm X := by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [HomogeneousLocalization.Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    all_goals rfl
  rw [h,AlgEquiv.apply_symm_apply]

theorem chart_zero_preimage_one :
    JLineAtlas318.chart R 0⁻¹ᵁ(JLineAtlas318.chart R 1 ''ᵁ ⊤)=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial R):=by
  rw [Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading R)
    (MvPolynomial.isHomogeneous_X R (0:Fin 2)) (by omega)
    (MvPolynomial.isHomogeneous_X R (1:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv R 0)
    (HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (0:Fin 2)) (MvPolynomial.isHomogeneous_X R (1:Fin 2))))=_
  have h:HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (0:Fin 2)) (MvPolynomial.isHomogeneous_X R (1:Fin 2))=
      (JLineAtlas318.chartEquiv R 0).symm Polynomial.X:=by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [HomogeneousLocalization.Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    all_goals rfl
  rw [h,AlgEquiv.apply_symm_apply]
end NormalizedProjectiveChartIntersection318
