module
public import PELOriginalFunctionRegularEvaluation318
public import PELOriginalFunctionNormalizationTransfer318
public import PELOriginalTwoDimensionalNormalization318
public import PELOriginalNormalizationPrimitiveCertificate318
public section
noncomputable section
namespace PELOriginalPolynomialGrowthRegular318
open QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalPolynomialGrowthFunction318
open PELOriginalSectionMultiplication318 PELOriginalSexticRatioCover318
open PELOriginalChartPrimitiveSeparator318
open PELOriginalPolynomialGrowthFunction318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- A continuous function on the entire original candidate chart, with
an exact differentiable original-cover representative and polynomial
growth in the actual coordinates, is a regular WHOLE-chart element.
All finite models, primitive elements, denominator removal, norm
equations and integral-closure inputs are produced internally. -/
theorem every_function (F : Data τ hτ j) :
    ∃ a : CoordinateChart τ hτ j, ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      f a=F.onCandidate (toLocus τ hτ j f) := by
  have hn := (PELOriginalLevelPowerSections318.original_values_independent τ hτ 3).ne_zero j
  have hx : ∃ x : ComplexVectors, value τ hτ 3 j x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨x,hx⟩ := hx
  obtain ⟨g,hg,hf⟩ := PELOriginalTwoDimensionalNormalization318.exists_two_variable_normalization τ hτ j
  let R := MvPolynomial (Fin 2) ℂ
  let A := CoordinateChart τ hτ j
  let K := FractionRing R
  let L := FractionRing A
  letI : Algebra R A := g.toAlgebra
  letI : IsScalarTower ℂ R A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  letI : Module.Finite R A := hf
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : Module.Finite K L := WholeFiniteFractionExtension318.finite R A
  obtain ⟨c,hc,hsep⟩ := exists_primitive_separator τ hτ j K ∅ Set.finite_empty
  let t := weightedRatioElement τ hτ j c
  have ht : PELOriginalSexticNormalizationTransfer318.Primitive τ hτ j g hg t := hc
  obtain ⟨d,hd,hgd,H,y,hy,hvalues⟩ :=
    PELOriginalFunctionNormalizationTransfer318.exists_transfer τ hτ j x hx F g hf hg t ht
  apply PELOriginalFunctionRegularEvaluation318.exists_regular τ hτ j g hg hf t d hd H F
  intro v hv f hbase
  apply hvalues v hv f
  ext r
  exact hbase r

/-- Exact evaluation of the same WHOLE regular element on every
original covering representative, including every former denominator
boundary. This is a chart-ring section, not only a rational formula. -/
theorem every_function_on_cover (F : Data τ hτ j) :
    ∃ a : CoordinateChart τ hτ j, ∀ z : ComplexVectors,
      ∀ hz : value τ hτ 3 j z ≠ 0,
      algebraEvaluation τ hτ z j hz a=F.onCover z := by
  obtain ⟨a,ha⟩ := every_function τ hτ j F
  refine ⟨a,?_⟩
  intro z hz
  have h := ha (algebraEvaluation τ hτ z j hz)
  have he : toLocus τ hτ j (algebraEvaluation τ hτ z j hz)=
      (⟨PELOriginalAllLevelHolomorphicMap318.ratioVector τ hτ 1 j z,
        PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ : Locus τ hτ j) := by
    apply Subtype.ext
    exact PELOriginalFullCandidatePoints318.pointVector_original τ hτ j z hz
  rw [he,F.original] at h
  exact h

end PELOriginalPolynomialGrowthRegular318
