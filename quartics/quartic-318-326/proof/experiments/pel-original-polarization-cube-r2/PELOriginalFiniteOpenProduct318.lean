module
public import PELOriginalFiniteOpenPointEvaluations318
public import ActualFinitePrincipalRestriction318
public section
noncomputable section
namespace PELOriginalFiniteOpenProduct318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedFiniteOpen318 PELOriginalCandidateAffineCharts318
open PELOriginalChartSectionField318 ActualPrincipalOpenRestriction318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

@[expose] def baseRestriction (p d : BasePolynomial) :
    Localization.Away p →+* Localization.Away (p*d) :=
  restriction p (p*d) (dvd_mul_right p d)

@[expose] def sourceRestriction (x : ComplexVectors) (p d : BasePolynomial) :
    Localization.Away (polynomialMap τ hτ j x p) →+*
      Localization.Away (polynomialMap τ hτ j x (p*d)) :=
  restriction _ _ (map_dvd (polynomialMap τ hτ j x).toRingHom (dvd_mul_right p d))

@[simp] theorem sourceRestriction_original (x : ComplexVectors) (p d : BasePolynomial)
    (a : CoordinateChart τ hτ j) :
    sourceRestriction τ hτ j x p d (algebraMap (CoordinateChart τ hτ j) _ a) =
      algebraMap (CoordinateChart τ hτ j) _ a :=
  restriction_source _ _ _ a

@[reassoc] theorem original_candidate_square (x : ComplexVectors) (p d : BasePolynomial) :
    Spec.map (CommRingCat.ofHom (sourceRestriction τ hτ j x p d)) ≫
      localizedChart τ hτ j x p = localizedChart τ hτ j x (p*d) := by
  rw [localizedChart,←Category.assoc]
  change (Spec.map (CommRingCat.ofHom (restriction _ _ _)) ≫ _) ≫ _ = _
  rw [source_composition]
  rfl

theorem cartesian (x : ComplexVectors) (p d : BasePolynomial) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (sourceRestriction τ hτ j x p d)))
      (localizedProjection τ hτ j x (p*d))
      (localizedProjection τ hτ j x p)
      (Spec.map (CommRingCat.ofHom (baseRestriction p d))) :=
  ActualFinitePrincipalRestriction318.cartesian (polynomialMap τ hτ j x).toRingHom
    p (p*d) (dvd_mul_right p d)

/-- Combining any additional nonzero base denominator with the finite
one retains finiteness, actual original analytic meeting and ALL exact
complex evaluations of the two projected functions. The source is the
same original principal preimage, not an adjoined auxiliary component. -/
theorem product_open (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0)
    (p d : BasePolynomial) (hp : p ≠ 0) (hd : d ≠ 0)
    (hf : (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p).Finite) :
    p*d ≠ 0 ∧
    (Localization.awayMap (polynomialMap τ hτ j x).toRingHom (p*d)).Finite ∧
    (∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
      PELOriginalChartAnalyticEvaluation318.algebraEvaluation τ hτ z j hz
        (polynomialMap τ hτ j x (p*d)) ≠ 0) ∧
    ∀ (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v (p*d) ≠ 0),
      ∃ q : Spec (CommRingCat.of ℂ) ⟶
        Spec (CommRingCat.of (Localization.Away (polynomialMap τ hτ j x (p*d)))),
        q ≫ localizedProjection τ hτ j x (p*d) =
          ComplexPolynomialOpenPoints318.point (p*d) v hv ∧
        q ≫ localizedChart τ hτ j x (p*d) ≫
          PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _ := by
  have hpd : p*d ≠ 0 := mul_ne_zero hp hd
  have hfin := ActualFinitePrincipalRestriction318.finite_product
    (polynomialMap τ hτ j x).toRingHom p d hf
  exact ⟨hpd,hfin,
    PELOriginalFiniteOpenAnalyticMeeting318.meets_original_patch τ hτ j x hx (p*d) hpd,
    fun v hv => PELOriginalFiniteOpenComplexPoints318.exists_localized_point
      τ hτ j x hx (p*d) hfin v hv⟩
end PELOriginalFiniteOpenProduct318
