module
public import PELOriginalProjectedFiniteOpen318
public section
noncomputable section
namespace PELOriginalFiniteOpenAnalyticMeeting318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedFiniteOpen318 PELOriginalProjectedChartIndependence318
open PELOriginalChartAnalyticEvaluation318 PELOriginalLevelThreeLocalImage318
open PELOriginalAllLevelHolomorphicMap318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- Literal polynomial evaluation in the produced pair is evaluation
at the SAME actual projected ratio vector. -/
theorem polynomial_evaluation (x z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (p : BasePolynomial) :
    algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x p) =
      MvPolynomial.eval (localProjection τ hτ x j (ratioVector τ hτ 1 j z)) p := by
  have hm : (algebraEvaluation τ hτ z j hz).comp (polynomialMap τ hτ j x) =
      MvPolynomial.aeval (localProjection τ hτ x j (ratioVector τ hτ 1 j z)) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply,polynomialMap_X,MvPolynomial.aeval_X,projected_evaluation]
  exact AlgHom.congr_fun hm p

/-- A nonzero base polynomial CANNOT vanish on the produced local
analytic projection neighborhood. Thus every finite-open denominator
has a genuine original point in its inverse image, within the same
original local chart; nonemptiness is not inferred from generic data. -/
theorem meets_original_patch (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) (p : BasePolynomial) (hp0 : p ≠ 0) :
    ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
      algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x p) ≠ 0 := by
  obtain ⟨W,hW,hWx,ht,hg,hU,hproj,himage⟩ := local_holomorphic_image τ hτ x j hx
  have hn : ∃ w ∈ W, MvPolynomial.eval w p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp0 (OpenComplexPolynomialIndependence318.eq_zero_of_open p W hW ⟨_,hWx⟩ h)
  obtain ⟨w,hw,hp⟩ := hn
  let z : ComplexVectors := (parameterChart τ hτ x j hx).symm w
  have hz : value τ hτ 3 j z ≠ 0 := (hU w hw).2
  refine ⟨z,hz,?_⟩
  rw [polynomial_evaluation]
  have he : localProjection τ hτ x j (ratioVector τ hτ 1 j z) = w := hproj w hw
  rwa [he]

/-- Actual finite projection AND actual original analytic meeting are
produced together. Neither image equality nor an unramified locus is
assumed or concluded. -/
theorem finite_open_with_original_point (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ p : BasePolynomial, p ≠ 0 ∧
      AlgebraicGeometry.IsFinite (localizedProjection τ hτ j x p) ∧
      ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
        algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x p) ≠ 0 := by
  obtain ⟨p,hp,hf⟩ := actual_finite_open τ hτ j x hx
  exact ⟨p,hp,hf,meets_original_patch τ hτ j x hx p hp⟩
end PELOriginalFiniteOpenAnalyticMeeting318
