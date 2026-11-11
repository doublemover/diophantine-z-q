module
public import PELOriginalSexticInterpolationGrowth318
public import PELOriginalSexticInterpolationDifferentiable318
public import LocalizedDifferentiablePolynomialFamily318
public section
noncomputable section
namespace PELOriginalSexticLocalizedPolynomial318
open Polynomial QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalOpenPrimitiveSheets318
open PELOriginalSexticRootInterpolation318 PELOriginalSectionMultiplication318
open PELOriginalLocalizedEvaluationSquare318 PELOriginalPrimitiveLocalReconstruction318
open PELOriginalSexticRatioCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- The actual whole sextic section ratio is one polynomial in the
original primitive coordinate with coefficients in the SAME original
base localization. All growth and differentiability premises have been
produced from the actual section and the full original root realization. -/
theorem exists_polynomial (hd : d ≠ 0) (hm : Q.Monic) (hs : Q.Separable)
    (s : homogeneous τ hτ 6)
    (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he)) :
    ∃ H : Polynomial (Localization.Away d), H.natDegree ≤ Q.natDegree ∧
      (∀ v (hv : MvPolynomial.eval v d ≠ 0),
        H.map (ComplexPolynomialOpenPoints318.evaluation d v hv) =
          interpolant τ hτ j x d Q e he hm s v) ∧
      ∀ z : originalDomain τ hτ j x d,
        H.eval₂ (ComplexPolynomialOpenPoints318.evaluation d
          (projectedVector τ hτ j x z.val) z.property.2)
          (primitiveValue τ hτ j x d Q e z.val) = coverRatio τ hτ j s z.val := by
  obtain ⟨M,N,C,hC,hb⟩ := PELOriginalSexticInterpolationGrowth318.coefficient_growth
    τ hτ j x d Q e he hm hs s honto
  obtain ⟨H,hdeg,hH⟩ := LocalizedDifferentiablePolynomialFamily318.exists_polynomial d hd
    (interpolant τ hτ j x d Q e he hm s) Q.natDegree M N C hC
    (fun v hv => Polynomial.natDegree_le_of_degree_le
      (LocalizedRootInterpolation318.degree_lt d Q hm hs
        (rootValue τ hτ j x d Q e he s) v hv).le)
    (fun n v hv => PELOriginalSexticInterpolationDifferentiable318.coefficient_differentiable
      τ hτ j x d Q e he hs honto hm s v hv n)
    (fun n v hv => hb v hv n)
  refine ⟨H,hdeg,hH,?_⟩
  intro z
  have h := interpolant_original τ hτ j x d Q e he hm s z
  rw [←hH _ z.property.2,Polynomial.eval_map] at h
  exact h
end PELOriginalSexticLocalizedPolynomial318
