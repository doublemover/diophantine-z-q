module
public import PELOriginalFiniteOpenLyingOver318
public import FiniteSurjectiveAlgebraicallyClosedPoints318
public import ComplexPolynomialOpenPoints318
public section
noncomputable section
namespace PELOriginalFiniteOpenComplexPoints318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedFiniteOpen318 PELOriginalCandidateAffineCharts318
open PELOriginalChartSectionField318 PELOriginalFiniteOpenBaseChange318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- Every literal complex vector in the produced polynomial base open
has a genuine Spec(C)-valued point in the WHOLE original localized
candidate chart. The exact projection and original C-structure are
retained. No membership in the original analytic image is asserted. -/
theorem exists_localized_point (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) (p : BasePolynomial)
    (hf : (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p).Finite)
    (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v p ≠ 0) :
    ∃ q : Spec (CommRingCat.of ℂ) ⟶
        Spec (CommRingCat.of (Localization.Away (polynomialMap τ hτ j x p))),
      q ≫ localizedProjection τ hτ j x p = ComplexPolynomialOpenPoints318.point p v hv ∧
      q ≫ localizedChart τ hτ j x p ≫
        PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _ := by
  letI : IsFinite (localizedProjection τ hτ j x p) := (IsFinite.SpecMap_iff _).mpr hf
  letI : Surjective (localizedProjection τ hτ j x p) :=
    PELOriginalFiniteOpenLyingOver318.finite_open_surjective τ hτ j x hx p hf
  obtain ⟨q,hq,hC⟩ := FiniteSurjectiveAlgebraicallyClosedPoints318.exists_lift_over
    (localizedProjection τ hτ j x p)
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (Localization.Away (polynomialMap τ hτ j x p)))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away p))))
    (projection_over_complex_base τ hτ j x p)
    (ComplexPolynomialOpenPoints318.point p v hv)
    (ComplexPolynomialOpenPoints318.over_complex p v hv)
  exact ⟨q,hq,by rw [original_complex_base]; exact hC⟩

/-- The lift has exactly the prescribed values of the original two
projected functions, expressed as an equality of actual Scheme maps. -/
@[reassoc] theorem original_pair_evaluation (x : ComplexVectors) (p : BasePolynomial)
    (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v p ≠ 0)
    (q : Spec (CommRingCat.of ℂ) ⟶
      Spec (CommRingCat.of (Localization.Away (polynomialMap τ hτ j x p))))
    (hq : q ≫ localizedProjection τ hτ j x p = ComplexPolynomialOpenPoints318.point p v hv) :
    q ≫ Spec.map (CommRingCat.ofHom (algebraMap (CoordinateChart τ hτ j)
        (Localization.Away (polynomialMap τ hτ j x p)))) ≫
      Spec.map (CommRingCat.ofHom (polynomialMap τ hτ j x).toRingHom) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id ℂ) v)) := by
  rw [←projection_square,←Category.assoc,hq,
    ComplexPolynomialOpenPoints318.original_evaluation]

/-- The denominator is PRODUCED from the actual chart, after which
all complex base values outside its zero set have genuine lifts. -/
theorem produced_complex_lifts (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ p : BasePolynomial, p ≠ 0 ∧ IsFinite (localizedProjection τ hτ j x p) ∧
      ∀ (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v p ≠ 0),
      ∃ q : Spec (CommRingCat.of ℂ) ⟶
          Spec (CommRingCat.of (Localization.Away (polynomialMap τ hτ j x p))),
        q ≫ localizedProjection τ hτ j x p = ComplexPolynomialOpenPoints318.point p v hv ∧
        q ≫ localizedChart τ hτ j x p ≫
          PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _ := by
  obtain ⟨p,hp,hf⟩ := exists_polynomial_finite_open τ hτ j x hx
  exact ⟨p,hp,(IsFinite.SpecMap_iff _).mpr hf,
    fun v hv => exists_localized_point τ hτ j x hx p hf v hv⟩
end PELOriginalFiniteOpenComplexPoints318
