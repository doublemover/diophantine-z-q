module
public import PELOriginalPrimitiveSeparableOpen318
public import LocalizedPrimitiveRootChart318
public section
noncomputable section
namespace PELOriginalPrimitiveAnalyticCharts318
open Polynomial
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedGenericFinite318 PELOriginalPrimitiveSeparableOpen318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalCandidateAffineCharts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Root charts for the SAME produced primitive equation and SAME two
projected coordinates. This applies at all roots on the produced open,
including roots not yet identified with the original analytic image.
The full candidate-order identification is a separate algebraic input. -/
theorem produced_primitive_charts (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : PolynomialBase, ∃ hd : d ≠ 0,
    ∃ Q A B : Polynomial (Localization.Away d),
      Q.map (FractionFiniteCoefficientLift318.toField PolynomialBase RationalBase d hd) =
        rationalEquation τ hτ j x hx ∧
      Q.Monic ∧ A*Q+B*Q.derivative = 1 ∧
      Q.natDegree = Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j) ∧
      ∀ p : AnalyticParameterizedRootChart318.ZeroLocus
          (LocalizedPrimitiveRootChart318.equation d Q),
        MvPolynomial.eval p.val.1 d ≠ 0 →
        ∃ e : OpenPartialHomeomorph
            (AnalyticParameterizedRootChart318.ZeroLocus
              (LocalizedPrimitiveRootChart318.equation d Q)) (Fin 2 → ℂ),
          p ∈ e.source ∧ (∀ q, e q = q.val.1) ∧
          AnalyticOnNhd ℂ (fun w => (e.symm w).val) e.target := by
  obtain ⟨d,hd,Q,A,B,hQ,hm,hAB,hdeg⟩ := exists_separable_open τ hτ j x hx
  have hs : Q.Separable := (Polynomial.separable_def' Q).mpr ⟨A,B,hAB⟩
  exact ⟨d,hd,Q,A,B,hQ,hm,hAB,hdeg,
    fun p hp => LocalizedPrimitiveRootChart318.exists_root_chart d Q hs p hp⟩
end PELOriginalPrimitiveAnalyticCharts318
