module
public import PELOriginalCommonPrimitiveOpen318
public import ActualPrimitiveQuotient318
public import ActualPrimitiveRestriction318
public section
noncomputable section
namespace PELOriginalMonogenicOrder318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalPrimitiveSeparableOpen318
open PELOriginalProjectedFiniteOpen318 PELOriginalProjectedFieldSquare318
open ActualPrincipalOpenRestriction318 FractionFiniteCoefficientLift318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFiniteType : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The WHOLE original candidate chart over one produced nonzero base
open is actually the monogenic quotient of its original primitive
minimal equation. The equivalence fixes every base coefficient and
sends the quotient root to the same regular original field generator.
Monicity and separability survive the extra denominator restriction. -/
theorem exists_original_order_equiv (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, ∃ hd : d ≠ 0,
    ∃ ha : polynomialMap τ hτ j x d ≠ 0,
    ∃ Q : Polynomial (Localization.Away d),
    ∃ β : Localization.Away (polynomialMap τ hτ j x d),
      Q.map (toField BasePolynomial (FractionRing BasePolynomial) d hd) =
        rationalEquation τ hτ j x hx ∧
      Q.Monic ∧ Q.Separable ∧
      toField (CoordinateChart τ hτ j) (OriginalField τ hτ j)
        (polynomialMap τ hτ j x d) ha β = generator τ hτ j x hx ∧
      ∃ e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d),
        e (AdjoinRoot.root Q) = β ∧
        ∀ a : Localization.Away d,
          e (AdjoinRoot.of Q a) =
            Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a := by
  let A := CoordinateChart τ hτ j
  let K := OriginalField τ hτ j
  let f := polynomialMap τ hτ j x
  have hi : Function.Injective f :=
    PELOriginalProjectedChartIndependence318.independent τ hτ x j hx
  obtain ⟨p,hp,hap,βp,hβp,hgen⟩ :=
    PELOriginalCommonPrimitiveOpen318.exists_whole_order_generator τ hτ j x hx
  obtain ⟨q,hq,Q,U,V,hQ,hm,hsep,hdeg⟩ := exists_separable_open τ hτ j x hx
  let d := p*q
  have hd : d ≠ 0 := mul_ne_zero hp hq
  have ha : f d ≠ 0 := by simpa only [map_zero] using hi.ne hd
  let rA := restriction (f p) (f d) (map_dvd f.toRingHom (dvd_mul_right p q))
  let rB := restriction q d (dvd_mul_left q p)
  let β : Localization.Away (f d) := rA βp
  let QD : Polynomial (Localization.Away d) := Q.map rB
  let φ := toField A K (f d) ha
  let g := Localization.awayMap f.toRingHom d
  let u := (rationalEquivalence τ hτ j x hx).toRingHom.comp
    (toField BasePolynomial (FractionRing BasePolynomial) d hd)
  have hu : Function.Injective u := (rationalEquivalence τ hτ j x hx).injective.comp
    (toField_injective BasePolynomial (FractionRing BasePolynomial) d hd)
  have hβ : φ β = generator τ hτ j x hx := by
    have hr := FractionPrincipalCompatibility318.restriction_field A K
      (f p) (f d) hap ha (map_dvd f.toRingHom (dvd_mul_right p q))
    change (φ.comp rA) βp = _
    rw [hr]
    exact hβp
  have hQD : QD.map (toField BasePolynomial (FractionRing BasePolynomial) d hd) =
      rationalEquation τ hτ j x hx := by
    rw [QD,Polynomial.map_map,
      FractionPrincipalCompatibility318.restriction_field BasePolynomial
        (FractionRing BasePolynomial) q d hq hd (dvd_mul_left q p),hQ]
  have hmin : QD.map u = minpoly (BaseField τ hτ j x) (generator τ hτ j x hx) := by
    rw [u, ← Polynomial.map_map,hQD,original_equation]
    rfl
  have hsquare : φ.comp g = (algebraMap (BaseField τ hτ j x) K).comp u := by
    simpa only [rationalEmbedding,RingHom.comp_assoc] using
      localized_coefficient_square τ hτ j x hx d hd ha
  have hroot : QD.eval₂ g β = 0 := by
    apply toField_injective A K (f d) ha
    change φ (QD.eval₂ g β) = φ 0
    rw [Polynomial.hom_eval₂,hsquare,hβ,map_zero]
    have he := minpoly.aeval (BaseField τ hτ j x) (generator τ hτ j x hx)
    rw [←hmin,Polynomial.aeval_def,Polynomial.eval₂_map] at he
    exact he
  have hsurj : Function.Surjective (Polynomial.eval₂RingHom g β) :=
    ActualPrimitiveRestriction318.polynomial_surjective ℂ BasePolynomial A f p q βp hgen
  let e : AdjoinRoot QD ≃+* Localization.Away (f d) :=
    RingEquiv.ofBijective (AdjoinRoot.lift g β hroot)
      ⟨ActualPrimitiveQuotient318.lift_injective u hu g φ β
          (generator τ hτ j x hx) hsquare hβ QD (hm.map rB) hmin hroot,
        ActualPrimitiveQuotient318.lift_surjective g β QD hroot hsurj⟩
  refine ⟨d,hd,ha,QD,β,hQD,hm.map rB,?_,hβ,e,?_,?_⟩
  · exact ((Polynomial.separable_def' Q).mpr ⟨U,V,hsep⟩).map
  · exact AdjoinRoot.lift_root hroot
  · intro a
    exact AdjoinRoot.lift_of hroot
end PELOriginalMonogenicOrder318
