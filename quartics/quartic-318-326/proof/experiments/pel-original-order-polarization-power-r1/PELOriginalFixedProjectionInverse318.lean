module
public import PELOriginalPrimitiveLocalReconstruction318
public import PELOriginalMonogenicOrder318
public import ImmersedGraphProjection318
public section
noncomputable section
namespace PELOriginalFixedProjectionInverse318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalProjectedGenericFinite318 PELOriginalProjectedPrimitivePolynomial318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLevelThreeLocalImage318
open PELOriginalLocalizedEvaluationSquare318 FractionFiniteCoefficientLift318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)

/-- The ACTUAL original factorization now supplies the missing input to
the fixed-projection inverse theorem. The projection is the one chosen
at x, but the local inverse is produced at EVERY valid original z. -/
theorem fixed_projection_chart (d : BasePolynomial)
    (Q : Polynomial (Localization.Away d)) (hs : Q.Separable)
    (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
    (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
      Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0)
    (hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0) :
    ∃ c : OpenPartialHomeomorph ComplexVectors ComplexVectors,
      z ∈ c.source ∧ (∀ w, c w = projectedVector τ hτ j x w) ∧
      ContDiffAt ℂ 1 c.symm (projectedVector τ hτ j x z) := by
  obtain ⟨G,hG,hfactor⟩ :=
    PELOriginalPrimitiveLocalReconstruction318.exists_local_reconstruction
      τ hτ j x d Q e he hs z hz hv
  have hf := PELOriginalLevelThetaStrictDerivative318.ratio_contDiffAt τ hτ 1 j z hz
  have hp : ContDiffAt ℂ 1 (projectedVector τ hτ j x) z :=
    (localProjection τ hτ x j).contDiff.contDiffAt.comp z hf
  exact ImmersedGraphProjection318.exists_projection_chart
    (ratioVector τ hτ 1 j) (projectedVector τ hτ j x) G z
    (hf.differentiableAt (by norm_num)) hp hG hfactor
    (PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ z j hz)

local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- One PRODUCED nonzero base open and the actual primitive equation
work uniformly for ALL original points above it. The original generator,
whole-order equivalence and base maps remain in the same certificate.
This is local inverse realization, not yet global sheet exhaustion. -/
theorem exists_all_original_charts (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, ∃ hd : d ≠ 0,
    ∃ ha : polynomialMap τ hτ j x d ≠ 0,
    ∃ Q : Polynomial (Localization.Away d),
    ∃ β : Localization.Away (polynomialMap τ hτ j x d),
      Q.map (toField BasePolynomial (FractionRing BasePolynomial) d hd) =
        rationalEquation τ hτ j x hx ∧ Q.Monic ∧ Q.Separable ∧
      toField (CoordinateChart τ hτ j) (OriginalField τ hτ j)
        (polynomialMap τ hτ j x d) ha β = generator τ hτ j x hx ∧
      ∃ e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d),
        e (AdjoinRoot.root Q) = β ∧
        (∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
          Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a) ∧
      ∀ (z : ComplexVectors), value τ hτ 3 j z ≠ 0 →
        MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0 →
        ∃ c : OpenPartialHomeomorph ComplexVectors ComplexVectors,
          z ∈ c.source ∧ (∀ w, c w = projectedVector τ hτ j x w) ∧
          ContDiffAt ℂ 1 c.symm (projectedVector τ hτ j x z) := by
  obtain ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he⟩ :=
    PELOriginalMonogenicOrder318.exists_original_order_equiv τ hτ j x hx
  exact ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he,
    fun z hz hv => fixed_projection_chart τ hτ j x d Q hs e he z hz hv⟩
end PELOriginalFixedProjectionInverse318
