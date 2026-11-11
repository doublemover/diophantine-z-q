module
public import PELOriginalMonogenicOrder318
public import BasePreservingAffinePoints318
public section
noncomputable section
namespace PELOriginalCandidateSimpleFibers318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalPrimitiveSeparableOpen318
open PELOriginalProjectedFiniteOpen318 FractionFiniteCoefficientLift318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- All genuine complex-valued fibers of the WHOLE original candidate
on the produced base open have exactly the original generic degree.
Their original primitive coordinate is simple at EVERY point. Neither
analytic-image membership nor topological sheet exhaustion is assumed. -/
theorem produced_candidate_fibers (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, ∃ hd : d ≠ 0,
    ∃ Q : Polynomial (Localization.Away d),
    ∃ β : Localization.Away (polynomialMap τ hτ j x d),
      Q.map (toField BasePolynomial (FractionRing BasePolynomial) d hd) =
        rationalEquation τ hτ j x hx ∧ Q.Monic ∧ Q.Separable ∧
      ∀ (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0),
        Nat.card (BasePreservingAffinePoints318.SchemePoints
          (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
          (ComplexPolynomialOpenPoints318.evaluation d v hv)) =
          Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j) ∧
        ∀ f : BasePreservingAffinePoints318.Points
            (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
            (ComplexPolynomialOpenPoints318.evaluation d v hv),
          (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).derivative.eval
            (f.val β) ≠ 0 := by
  obtain ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he⟩ :=
    PELOriginalMonogenicOrder318.exists_original_order_equiv τ hτ j x hx
  have hdegree : Q.natDegree = Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j) := by
    have hn := Polynomial.natDegree_map_eq_of_injective
      (toField_injective BasePolynomial (FractionRing BasePolynomial) d hd) Q
    rw [hQ,rational_degree] at hn
    exact hn.symm
  refine ⟨d,hd,Q,β,hQ,hm,hs,?_⟩
  intro v hv
  refine ⟨(BasePreservingAffinePoints318.point_count _ _ Q e he hm hs).trans hdegree,?_⟩
  intro f
  have hf := BasePreservingAffinePoints318.every_point_simple _ _ Q e he hs f
  rwa [heβ] at hf
end PELOriginalCandidateSimpleFibers318
