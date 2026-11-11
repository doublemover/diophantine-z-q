module
public import PELOriginalProjectedGenericFinite318
public import AlgebraicFiniteTypeFiniteOpen318
public section
noncomputable section
namespace PELOriginalProjectedFiniteOpen318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedGenericFinite318
open PELOriginalChartSectionField318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFiniteType : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
abbrev BasePolynomial := MvPolynomial (Fin 2) ℂ

/-- The exact two analytic projection functions, regarded as a genuine
polynomial-algebra map into the SAME full candidate chart. -/
@[expose] def polynomialMap (x : ComplexVectors) :
    BasePolynomial →ₐ[ℂ] CoordinateChart τ hτ j :=
  MvPolynomial.aeval (projectedFunction τ hτ x j)
@[simp] theorem polynomialMap_X (x : ComplexVectors) (k : Fin 2) :
    polynomialMap τ hτ j x (MvPolynomial.X k) = projectedFunction τ hτ x j k :=
  MvPolynomial.aeval_X _ _

/-- The genuine full chart is finite over a nonempty polynomial base
open after inverting one produced nonzero polynomial. No replacement
normalization coordinates or supplied denominator is used. -/
theorem exists_polynomial_finite_open (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ p : BasePolynomial, p ≠ 0 ∧
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p).Finite := by
  let A := CoordinateChart τ hτ j
  let R := projectedBase τ hτ j x
  let pair := projectedFunction τ hτ x j
  have hp : AlgebraicIndependent ℂ pair := independent τ hτ x j hx
  letI : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R A
  letI : Algebra.IsAlgebraic R A :=
    IndependentPairGenericFinite318.algebraic_over_pair A pair hp
      (PELOriginalAffineChartTranscendence318.actual_chart_trdeg_le_two τ hτ j)
  have he : (algebraMap R A).comp hp.aevalEquiv.toRingHom =
      (polynomialMap τ hτ j x).toRingHom := by
    ext p
    exact hp.algebraMap_aevalEquiv p
  obtain ⟨p,hp0,hfinite⟩ := AlgebraicFiniteTypeFiniteOpen318.exists_finite_open_of_equiv
    R A BasePolynomial hp.aevalEquiv.toRingEquiv
  exact ⟨p,hp0,he ▸ hfinite⟩

@[expose] def localizedProjection (x : ComplexVectors) (p : BasePolynomial) :
    Spec (CommRingCat.of (Localization.Away (polynomialMap τ hτ j x p))) ⟶
      Spec (CommRingCat.of (Localization.Away p)) :=
  Spec.map (CommRingCat.ofHom
    (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p))
@[expose] def localizedChart (x : ComplexVectors) (p : BasePolynomial) :
    Spec (CommRingCat.of (Localization.Away (polynomialMap τ hτ j x p))) ⟶
      PELOriginalReducedProjectiveCandidate318.candidate τ hτ :=
  Spec.map (CommRingCat.ofHom (algebraMap (CoordinateChart τ hτ j) _)) ≫ chartMap τ hτ j

/-- The original scalar square is retained on ALL points of the
localized chart, not only on the original analytic image. -/
@[reassoc] theorem projection_square (x : ComplexVectors) (p : BasePolynomial) :
    localizedProjection τ hτ j x p ≫
      Spec.map (CommRingCat.ofHom (algebraMap BasePolynomial (Localization.Away p))) =
    Spec.map (CommRingCat.ofHom (algebraMap (CoordinateChart τ hτ j)
      (Localization.Away (polynomialMap τ hτ j x p)))) ≫
      Spec.map (CommRingCat.ofHom (polynomialMap τ hτ j x).toRingHom) := by
  rw [localizedProjection,←Spec.map_comp,←Spec.map_comp]
  congr 1
  ext a
  simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq]

theorem actual_finite_open (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0) :
    ∃ p : BasePolynomial, p ≠ 0 ∧ IsFinite (localizedProjection τ hτ j x p) := by
  obtain ⟨p,hp,hf⟩ := exists_polynomial_finite_open τ hτ j x hx
  exact ⟨p,hp,(IsFinite.SpecMap_iff _).mpr hf⟩
end PELOriginalProjectedFiniteOpen318
