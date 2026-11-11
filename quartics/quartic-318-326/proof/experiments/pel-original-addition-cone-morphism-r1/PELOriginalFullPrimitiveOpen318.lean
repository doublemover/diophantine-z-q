module
public import IrreducibleLocalizedSelectedFactor318
public import PELOriginalClopenPrimitiveSheets318
public import PELOriginalMonogenicOrder318
public section
noncomputable section
namespace PELOriginalFullPrimitiveOpen318
open Polynomial Set
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalProjectedGenericFinite318 PELOriginalProjectedPrimitivePolynomial318
open PELOriginalPrimitiveSeparableOpen318 PELOriginalRootCoordinates318
open PELOriginalOpenPrimitiveSheets318 PELOriginalClopenPrimitiveSheets318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (hx : value τ hτ 3 j x ≠ 0)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- The actual original primitive minimal equation, not a newly chosen
irreducible polynomial, forces the nonempty clopen original selection to
exhaust EVERY independent root over the whole SAME produced D(d). -/
theorem original_root_surjective (d : BasePolynomial) (hd : d ≠ 0)
    (Q : Polynomial (Localization.Away d))
    (hQ : Q.map (FractionFiniteCoefficientLift318.toField BasePolynomial
      (FractionRing BasePolynomial) d hd) = rationalEquation τ hτ j x hx)
    (hm : Q.Monic) (hs : Q.Separable)
    (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
    (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
      Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a) :
    Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he) := by
  let u : Localization.Away d →+* BaseField τ hτ j x :=
    (rationalEquivalence τ hτ j x hx).toRingHom.comp
      (FractionFiniteCoefficientLift318.toField BasePolynomial (FractionRing BasePolynomial) d hd)
  have hu : Function.Injective u := (rationalEquivalence τ hτ j x hx).injective.comp
    (FractionFiniteCoefficientLift318.toField_injective BasePolynomial (FractionRing BasePolynomial) d hd)
  have hirr : Irreducible (Q.map u) := by
    rw [u,←Polynomial.map_map,hQ,original_equation]
    exact equation_irreducible τ hτ j x hx
  intro q
  exact IrreducibleLocalizedSelectedFactor318.all_selected d hd Q hm hs
    (Set.range (originalOpenRootPoint τ hτ j x d Q e he))
    (selected_open τ hτ j x d Q e he hs) (selected_closed τ hτ j x d Q e he)
    (selected_nonempty τ hτ j x d Q e he hx hd) u hu hirr q

/-- A single actual denominator and whole-order certificate are chosen
ONCE. They retain the actual primitive generator and original rational
minimal equation, and the original root map is onto the entire candidate
root locus there. This is full common-open image equality, not just local
openness, nonempty intersection or dense selected sheets. -/
theorem exists_full_original_open :
    ∃ d : BasePolynomial, ∃ hd : d ≠ 0,
    ∃ ha : polynomialMap τ hτ j x d ≠ 0,
    ∃ Q : Polynomial (Localization.Away d),
    ∃ β : Localization.Away (polynomialMap τ hτ j x d),
      Q.map (FractionFiniteCoefficientLift318.toField BasePolynomial (FractionRing BasePolynomial) d hd) =
        rationalEquation τ hτ j x hx ∧ Q.Monic ∧ Q.Separable ∧
      FractionFiniteCoefficientLift318.toField (CoordinateChart τ hτ j) (OriginalField τ hτ j)
        (polynomialMap τ hτ j x d) ha β = generator τ hτ j x hx ∧
      ∃ e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d),
        e (AdjoinRoot.root Q) = β ∧
        ∃ he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
          Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a,
          Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he) := by
  obtain ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he⟩ :=
    PELOriginalMonogenicOrder318.exists_original_order_equiv τ hτ j x hx
  exact ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he,
    original_root_surjective τ hτ j x hx d hd Q hQ hm hs e he⟩
end PELOriginalFullPrimitiveOpen318
