module
public import PELOriginalFiniteUnramifiedProjection318
public import PELOriginalCandidateNormalizationTopology318
public import PELOriginalCandidateLocalGraph318
public section
noncomputable section
namespace PELOriginalCandidateNormalizationLocalInjection318
open Set QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationTransitions318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartEvaluationRegularity318 PELOriginalAllLevelHolomorphicMap318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateElementFunctions318
open PELOriginalCandidateAffineTopology318 PELOriginalLevelThreeLocalImage318
open PELOriginalFiniteUnramifiedProjection318 PELOriginalProjectedChartIndependence318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance discretePeriods : DiscreteTopology (P τ) :=
  PELOriginalPeriodLattice318.original_discrete τ hτ
local instance targetTopology : TopologicalSpace (PELOriginalAllLevelHolomorphicMap318.Target 1) :=
  ComplexProjectiveQuotientTopology318.topology (Label 3)

lemma pointVector_original (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    pointVector τ hτ j (algebraEvaluation τ hτ z j hz) = ratioVector τ hτ 1 j z := by
  funext i
  exact coordinate_evaluation τ hτ z j hz i

lemma elementValue_original (a : CoordinateChart τ hτ j)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    elementValue τ hτ j a (ratioVector τ hτ 1 j z) = evaluate τ hτ j a z := by
  rw [←pointVector_original τ hτ j z hz,pointVector_value]
  exact (evaluate_on_chart τ hτ j a z hz).symm

lemma projection_original
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    PELOriginalCandidateNormalizationTopology318.projection τ hτ j 2 g
      (ratioVector τ hτ 1 j z) = evaluationVector τ hτ j g z := by
  funext k
  exact elementValue_original τ hτ j _ z hz

/-- A local inverse for the original analytic normalization gives local
injectivity on the ENTIRE independently defined affine candidate. The
neighborhood is open in its actual ambient topology. In particular this
is not merely injectivity on a chosen primitive-root sheet. -/
theorem candidate_locally_injective
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0)
    (e : OpenPartialHomeomorph ComplexVectors ComplexVectors)
    (he : ∀ y, e y = evaluationVector τ hτ j g y) (hxe : x ∈ e.source) :
    ∃ N : Set (Locus τ hτ j), IsOpen N ∧
      toLocus τ hτ j (algebraEvaluation τ hτ x j hx) ∈ N ∧
      Set.InjOn (fun w : Locus τ hτ j =>
        PELOriginalCandidateNormalizationTopology318.projection τ hτ j 2 g w.val) N := by
  let t := PELOriginalPolarizationTransitions318.chart τ hτ x
  let D : Set ComplexVectors := e.source ∩ originalChartDomain τ hτ x j
  have hD : IsOpen D := e.open_source.inter (originalChartDomain_open τ hτ x j)
  have hDt : D ⊆ t.target := fun z hz => hz.2.1
  let U : Set (PELOriginalPolarizationTransitions318.Base τ) := t.symm '' D
  have hU : IsOpen U := t.isOpen_image_symm_of_subset_target hD hDt
  let N : Set (Locus τ hτ j) := sourcePoint τ hτ j ⁻¹' U
  have hN : IsOpen N := hU.preimage (sourcePoint_continuous τ hτ j)
  have hxN : toLocus τ hτ j (algebraEvaluation τ hτ x j hx) ∈ N := by
    refine ⟨x,⟨hxe,originalChartDomain_center τ hτ x j hx⟩,?_⟩
    have hpoint : toLocus τ hτ j (algebraEvaluation τ hτ x j hx) =
        (⟨ratioVector τ hτ 1 j x,
          PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j
            ⟨x,hx,rfl⟩⟩ : Locus τ hτ j) :=
      Subtype.ext (pointVector_original τ hτ j x hx)
    rw [hpoint,sourcePoint_original]
    rfl
  have representative (q : Locus τ hτ j) (hq : q ∈ N) :
      ∃ z ∈ D, q.val = ratioVector τ hτ 1 j z := by
    obtain ⟨z,hz,hzq⟩ := hq
    refine ⟨z,hz,?_⟩
    have hh := actual_original_formula τ hτ x j z
    change ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j
      (PELOriginalAllLevelProjectiveMap318.projectiveMap τ hτ 1 (t.symm z)) =
      ratioVector τ hτ 1 j z at hh
    rw [hzq,sourcePoint_image,
      (ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j).right_inv
        (mem_univ q.val)] at hh
    exact hh
  refine ⟨N,hN,hxN,?_⟩
  intro q hq r hr hqr
  obtain ⟨z,hz,hzq⟩ := representative q hq
  obtain ⟨w,hw,hwr⟩ := representative r hr
  rw [hzq,hwr,projection_original τ hτ j g z hz.2.2,
    projection_original τ hτ j g w hw.2.2] at hqr
  have hzw : z = w := e.injOn hz.1 hw.1 (by simpa only [he] using hqr)
  subst w
  exact Subtype.ext (hzq.trans hwr.symm)

/-- Every actual original point admits a WHOLE finite faithful
normalization that is locally injective on the full candidate itself. -/
theorem exists_finite_faithful_local_injection
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0) :
    ∃ g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j,
      g.Finite ∧ Function.Injective g ∧
      ∃ N : Set (Locus τ hτ j), IsOpen N ∧
        toLocus τ hτ j (algebraEvaluation τ hτ x j hx) ∈ N ∧
        Set.InjOn (fun w : Locus τ hτ j =>
          PELOriginalCandidateNormalizationTopology318.projection τ hτ j 2 g w.val) N := by
  obtain ⟨g,hf,hg,hd,e,he,hxe,hi⟩ := exists_finite_faithful_identity_chart τ hτ j x hx
  exact ⟨g,hf,hg,candidate_locally_injective τ hτ j g x hx e he hxe⟩
end PELOriginalCandidateNormalizationLocalInjection318
