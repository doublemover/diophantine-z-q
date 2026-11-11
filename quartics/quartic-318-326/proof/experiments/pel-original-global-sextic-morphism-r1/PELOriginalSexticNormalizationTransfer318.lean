module
public import PrimitiveFractionNormalizationTransfer318
public import PrincipalRestrictionEvaluation318
public import PELOriginalSexticLocalizedElement318
public section
noncomputable section
namespace PELOriginalSexticNormalizationTransfer318
open Polynomial QuaternionicRealPeriod318 FractionFiniteCoefficientLift318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalOpenPrimitiveSheets318
open PELOriginalSexticRootInterpolation318 PELOriginalSectionMultiplication318
open PELOriginalLocalizedEvaluationSquare318 PELOriginalPrimitiveLocalReconstruction318
open PELOriginalSexticRatioCover318 PELOriginalSexticChartRatios318
open PELOriginalCandidatePointEquivalence318 PELOriginalAllLevelHolomorphicMap318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Primitive-field generation uses the actual specified normalization
scalar action, not a new abstract identification of the chart field. -/
@[expose] def Primitive (g : BasePolynomial →ₐ[ℂ] CoordinateChart τ hτ j)
    (hginj : Function.Injective g) (t : CoordinateChart τ hτ j) : Prop :=
  letI : Algebra BasePolynomial (CoordinateChart τ hτ j) := g.toAlgebra
  letI : FaithfulSMul BasePolynomial (CoordinateChart τ hτ j) :=
    (faithfulSMul_iff_algebraMap_injective BasePolynomial (CoordinateChart τ hτ j)).mpr hginj
  Function.Surjective
    (Polynomial.aeval (algebraMap (CoordinateChart τ hτ j)
      (FractionRing (CoordinateChart τ hτ j)) t) :
      Polynomial (FractionRing BasePolynomial) →ₐ[FractionRing BasePolynomial]
        FractionRing (CoordinateChart τ hτ j))

/-- Transfer EVERY whole sextic ratio from its produced old chart open
to ANY actual faithful finite normalization and primitive field element.
All new root values are identified at every WHOLE algebra evaluation,
not only at points already presented on the old primitive cover. -/
theorem exists_transfer (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0)
    (s : homogeneous τ hτ 6)
    (g : BasePolynomial →ₐ[ℂ] CoordinateChart τ hτ j) (hg : g.Finite)
    (hginj : Function.Injective g) (t : CoordinateChart τ hτ j)
    (ht : Primitive τ hτ j g hginj t) :
    ∃ d : BasePolynomial, ∃ hd : d ≠ 0, ∃ hgd : g d ≠ 0,
    ∃ H : Polynomial (Localization.Away d),
    ∃ y : FractionRing (CoordinateChart τ hτ j),
      (toField (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j)) (g d) hgd)
        (H.eval₂ (Localization.awayMap g.toRingHom d)
          (algebraMap (CoordinateChart τ hτ j) (Localization.Away (g d)) t)) = y ∧
      ∀ v (hv : MvPolynomial.eval v d ≠ 0)
        (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ),
        f.toRingHom.comp g.toRingHom = MvPolynomial.eval₂Hom (RingHom.id ℂ) v →
        H.eval₂ (ComplexPolynomialOpenPoints318.evaluation d v hv) (f t) =
          candidateRatio τ hτ j s (toLocus τ hτ j f) := by
  let A := CoordinateChart τ hτ j
  let R := BasePolynomial
  letI : Algebra R A := g.toAlgebra
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hginj
  letI : Module.Finite R A := hg
  obtain ⟨d₀,hd₀,hb,Q,β,hQ,hm,hs,hβ,e,heβ,he,honto⟩ :=
    PELOriginalFullPrimitiveOpen318.exists_full_original_open τ hτ j x hx
  obtain ⟨a,ha,hOld⟩ := PELOriginalSexticLocalizedElement318.exists_element
    τ hτ j x d₀ Q e he hd₀ hm hs s honto
  let b := polynomialMap τ hτ j x d₀
  obtain ⟨d,hd,hgd,hbd,H,hH,hfield⟩ :=
    PrimitiveFractionNormalizationTransfer318.exists_polynomial R A b hb
      (IsIntegral.of_finite R b) a t ht
  refine ⟨d,hd,hgd,H,toField A (FractionRing A) b hb a,hfield,?_⟩
  intro v hv f hsq
  let vR : R →+* ℂ := MvPolynomial.eval₂Hom (RingHom.id ℂ) v
  have hbF := PrincipalRestrictionEvaluation318.source_ne_zero g.toRingHom d b hbd vR f.toRingHom hsq hv
  have htrans := PrincipalRestrictionEvaluation318.transferred_value g.toRingHom d b t hbd a H hH
    vR f.toRingHom hsq hv
  apply htrans.trans
  obtain ⟨z,hz,hf⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  have hdz : MvPolynomial.eval (projectedVector τ hτ j x z) d₀ ≠ 0 := by
    simpa only [hf,b,polynomial_evaluation] using hbF
  have hlocus : toLocus τ hτ j f =
      (⟨ratioVector τ hτ 1 j z,
        PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ : Locus τ hτ j) := by
    apply Subtype.ext
    rw [hf]
    exact PELOriginalFullCandidatePoints318.pointVector_original τ hτ j z hz
  rw [hlocus,candidate_original,hf]
  exact hOld ⟨z,hz,hdz⟩
end PELOriginalSexticNormalizationTransfer318
