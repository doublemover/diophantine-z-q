module
public import JLineAtlas318
public section
noncomputable section
namespace JLineOverlapOpen318
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact full overlap of the two standard charts of the actual contact line. -/
theorem chart_zero_preimage_one :
    JLineAtlas318.chart ℚ 0⁻¹ᵁ(JLineAtlas318.chart ℚ 1 ''ᵁ ⊤)=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial ℚ):=by
  rw [Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading ℚ)
    (isHomogeneous_X ℚ (0:Fin 2)) (by omega)
    (isHomogeneous_X ℚ (1:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv ℚ 0)
    (Away.isLocalizationElem (isHomogeneous_X ℚ (0:Fin 2)) (isHomogeneous_X ℚ (1:Fin 2))))=_
  have h:Away.isLocalizationElem (isHomogeneous_X ℚ (0:Fin 2)) (isHomogeneous_X ℚ (1:Fin 2))=
      (JLineAtlas318.chartEquiv ℚ 0).symm Polynomial.X:=by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]
end JLineOverlapOpen318
