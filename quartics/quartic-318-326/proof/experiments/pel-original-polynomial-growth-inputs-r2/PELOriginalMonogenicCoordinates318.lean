module
public import PELOriginalMonogenicOrder318
public import MonogenicOriginalCoordinates318
public section
noncomputable section
namespace PELOriginalMonogenicCoordinates318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalPrimitiveSeparableOpen318
open PELOriginalProjectedFiniteOpen318 FractionFiniteCoefficientLift318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- ALL original localized candidate coordinates are reconstructed by
fixed polynomials in the SAME primitive coordinate, simultaneously at
ALL base-preserving complex points of the entire original order. The
coefficients are regular on one produced polynomial base open. -/
theorem exists_original_coordinate_formulas (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
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
        (∀ c : Localization.Away d, e (AdjoinRoot.of Q c) =
          Localization.awayMap (polynomialMap τ hτ j x).toRingHom d c) ∧
      ∀ a : Localization.Away (polynomialMap τ hτ j x d),
        ∃ P : Polynomial (Localization.Away d),
          ∀ (v : Localization.Away d →+* ℂ)
            (f : BasePreservingAffinePoints318.Points
              (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) v),
            f.val a = P.eval₂ v (f.val β) := by
  obtain ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he⟩ :=
    PELOriginalMonogenicOrder318.exists_original_order_equiv τ hτ j x hx
  refine ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he,?_⟩
  intro a
  obtain ⟨P,hP,hformula⟩ := MonogenicOriginalCoordinates318.exists_expression _ Q e he a
  refine ⟨P,?_⟩
  intro v f
  simpa only [heβ] using hformula v f
end PELOriginalMonogenicCoordinates318
