module
public import PELOriginalProjectedFieldSquare318
public import ActualPrimitiveOrderGeneration318
public section
noncomputable section
namespace PELOriginalCommonPrimitiveOpen318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalPrimitiveSeparableOpen318
open PELOriginalProjectedFiniteOpen318 PELOriginalProjectedFieldSquare318
open ActualPrincipalOpenRestriction318 FractionFiniteCoefficientLift318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- On one PRODUCED nonzero polynomial base open, the same primitive
field generator is regular and generates the ENTIRE original candidate
chart localization. Both denominator restrictions and the coefficient
map are the literal original ones. This is not merely a statement in
the candidate fraction field, and includes every original chart element. -/
theorem exists_whole_order_generator (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, ∃ hd : d ≠ 0,
    ∃ ha : polynomialMap τ hτ j x d ≠ 0,
    ∃ β : Localization.Away (polynomialMap τ hτ j x d),
      toField (CoordinateChart τ hτ j) (OriginalField τ hτ j)
        (polynomialMap τ hτ j x d) ha β = generator τ hτ j x hx ∧
      Function.Surjective
        (Polynomial.eval₂RingHom
          (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) β) := by
  classical
  let A := CoordinateChart τ hτ j
  let K := OriginalField τ hτ j
  let f := polynomialMap τ hτ j x
  have hi : Function.Injective f :=
    PELOriginalProjectedChartIndependence318.independent τ hτ x j hx
  obtain ⟨p, hp, hap, βp, hβp⟩ :=
    PELOriginalPrimitiveRegularOpen318.exists_regular_primitive τ hτ j x hx
  obtain ⟨s, hs, q, hq, P, hP⟩ :=
    PELOriginalPrimitiveGeneratorExpressions318.exists_generator_expressions τ hτ j x hx
  let d := p * q
  have hd : d ≠ 0 := mul_ne_zero hp hq
  have ha : f d ≠ 0 := by simpa only [map_zero] using hi.ne hd
  let rA := restriction (f p) (f d) (map_dvd f.toRingHom (dvd_mul_right p q))
  let rB := restriction q d (dvd_mul_left q p)
  let β : Localization.Away (f d) := rA βp
  let φ := toField A K (f d) ha
  let g := Localization.awayMap f.toRingHom d
  have hβ : φ β = generator τ hτ j x hx := by
    have hr := FractionPrincipalCompatibility318.restriction_field A K
      (f p) (f d) hap ha (map_dvd f.toRingHom (dvd_mul_right p q))
    change (φ.comp rA) βp = _
    rw [hr]
    exact hβp
  have hc : φ.comp g = (rationalEmbedding τ hτ j x hx).comp
      (toField BasePolynomial (FractionRing BasePolynomial) d hd) :=
    localized_coefficient_square τ hτ j x hx d hd ha
  have hcr : (φ.comp g).comp rB =
      (rationalEmbedding τ hτ j x hx).comp
        (toField BasePolynomial (FractionRing BasePolynomial) q hq) := by
    rw [hc, RingHom.comp_assoc,
      FractionPrincipalCompatibility318.restriction_field BasePolynomial
        (FractionRing BasePolynomial) q d hq hd (dvd_mul_left q p)]
  have hg (a : A) (ha' : a ∈ s) :
      ∃ Q : Polynomial (Localization.Away d),
        Q.eval₂ g β = algebraMap A (Localization.Away (f d)) a := by
    let i : s := ⟨a, ha'⟩
    refine ⟨(P i).map rB, ?_⟩
    apply toField_injective A K (f d) ha
    change φ (Polynomial.eval₂ g β ((P i).map rB)) = φ _
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, hcr, hβ,
      toField_coefficient]
    have he := (hP i).1
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_map,
      rationalEmbedding, RingHom.comp_assoc] using he
  refine ⟨d, hd, ha, β, hβ, ?_⟩
  exact ActualPrimitiveOrderGeneration318.polynomial_surjective ℂ BasePolynomial A
    f d s hs β hg
end PELOriginalCommonPrimitiveOpen318
