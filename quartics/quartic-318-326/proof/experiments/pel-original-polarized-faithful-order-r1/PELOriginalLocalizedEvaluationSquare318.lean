module
public import PELOriginalLocalizedEvaluationRegularity318
public import PELOriginalProjectedFieldSquare318
public import BasePreservingAffinePoints318
public section
noncomputable section
namespace PELOriginalLocalizedEvaluationSquare318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalLevelThreeLocalImage318 PELOriginalAllLevelHolomorphicMap318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The SAME specified two projected ratios of the actual theta vector. -/
@[expose] def projectedVector (x z : ComplexVectors) : Fin 2 → ℂ :=
  localProjection τ hτ x j (ratioVector τ hτ 1 j z)

/-- ALL polynomial base coefficients commute with actual theta
evaluation, not only the two coordinate generators. -/
theorem polynomial_evaluation (x z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (P : BasePolynomial) :
    algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x P) =
      MvPolynomial.eval (projectedVector τ hτ j x z) P := by
  have he : (algebraEvaluation τ hτ z j hz).comp (polynomialMap τ hτ j x) =
      MvPolynomial.aeval (projectedVector τ hτ j x z) := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [AlgHom.comp_apply,polynomialMap_X,MvPolynomial.aeval_X,projected_evaluation]
    rfl
  exact congrArg (fun f : BasePolynomial →ₐ[ℂ] ℂ => f P) he

/-- The actual whole localized theta evaluation lies over precisely its
original projected base vector. The equality is of ENTIRE localization
ring maps, so denominators and all primitive coefficients are retained. -/
theorem localized_square (x z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (d : BasePolynomial)
    (hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0)
    (hd : algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x d) ≠ 0) :
    (PELOriginalLocalizedEvaluationRegularity318.evaluation τ hτ j
      (polynomialMap τ hτ j x d) z hz hd).comp
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) =
      ComplexPolynomialOpenPoints318.evaluation d (projectedVector τ hτ j x z) hv := by
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  ext a
  simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,PELOriginalLocalizedEvaluationRegularity318.evaluation_source,
    ComplexPolynomialOpenPoints318.evaluation_source]
  exact polynomial_evaluation τ hτ j x z hz a

/-- The actual original theta point is now a member of the very SAME
whole-order fiber-point type used by the monogenic reconstruction.
No comparison of related but different evaluations is left as a premise. -/
@[expose] def originalPoint (x z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (d : BasePolynomial)
    (hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0) :
    BasePreservingAffinePoints318.Points
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
      (ComplexPolynomialOpenPoints318.evaluation d (projectedVector τ hτ j x z) hv) := by
  have hd : algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x d) ≠ 0 := by
    rwa [polynomial_evaluation]
  exact ⟨PELOriginalLocalizedEvaluationRegularity318.evaluation τ hτ j
    (polynomialMap τ hτ j x d) z hz hd,localized_square τ hτ j x z hz d hv hd⟩

@[simp] theorem originalPoint_source (x z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) (d : BasePolynomial)
    (hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0)
    (a : CoordinateChart τ hτ j) :
    (originalPoint τ hτ j x z hz d hv).val
      (algebraMap (CoordinateChart τ hτ j) _ a) = algebraEvaluation τ hτ z j hz a :=
  PELOriginalLocalizedEvaluationRegularity318.evaluation_source τ hτ j
    (polynomialMap τ hτ j x d) z hz _ a
end PELOriginalLocalizedEvaluationSquare318
