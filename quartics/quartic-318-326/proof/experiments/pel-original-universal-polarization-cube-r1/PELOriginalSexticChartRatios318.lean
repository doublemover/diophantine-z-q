module
public import PELOriginalSexticSectionAlgebraicity318
public import PELOriginalCandidateAffineTopology318
public import PELOriginalPowerSectionDescent318
public section
noncomputable section
namespace PELOriginalSexticChartRatios318
open Set Filter Topology QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateAffineTopology318
open PELOriginalAllLevelProjectiveMap318 ComplexProjectiveQuotientTopology318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance targetTopology : TopologicalSpace (PELOriginalAllLevelHolomorphicMap318.Target 1) :=
  topology (Label 3)
local instance discretePeriods : DiscreteTopology (P τ) :=
  PELOriginalPeriodLattice318.original_discrete τ hτ

/-- The actual sextic section coefficient divided by the square of the
SAME original cubic chart coefficient. Both use the original selected
fiber gauge, which cancels in the ratio. -/
@[expose] def baseRatio (j : Label 3) (s : homogeneous τ hτ 6) (q : Base τ) : ℂ :=
  s.val q / ((thetaVector τ hτ 3 j).val q)^2

lemma local_ratio (j : Label 3) (s : homogeneous τ hτ 6)
    (a : ComplexVectors) (q : Base τ) (hq : q ∈ baseSet τ hτ a) :
    baseRatio τ hτ j s q =
      localCoefficient τ hτ 6 a s.val (chart τ hτ a q) /
        (localCoefficient τ hτ 3 a (thetaVector τ hτ 3 j).val (chart τ hτ a q))^2 := by
  rw [coefficient_formula,coefficient_formula,section_projection τ hτ a q hq]
  let c := transition τ hτ ((core τ hτ).indexAt q) a q
  have hc : c ≠ 0 := transition_nonzero τ hτ _ _ _
  change s.val q / ((thetaVector τ hτ 3 j).val q)^2 =
    (c^6*s.val q)/(c^3*(thetaVector τ hτ 3 j).val q)^2
  rw [mul_pow,←pow_mul]
  change _ = (c^6*s.val q)/(c^6*((thetaVector τ hτ 3 j).val q)^2)
  exact (mul_div_mul_left _ _ (pow_ne_zero 6 hc)).symm

/-- Continuity is derived in actual original line-bundle charts, rather
than treating the selected fiber coefficient as globally continuous. -/
theorem baseRatio_continuousAt (j : Label 3) (s : homogeneous τ hτ 6)
    (q : Base τ) (hj : (thetaVector τ hτ 3 j).val q ≠ 0) :
    ContinuousAt (baseRatio τ hτ j s) q := by
  let a := (core τ hτ).indexAt q
  have hq : q ∈ baseSet τ hτ a := (core τ hτ).mem_baseSet_at q
  have ht := (chart τ hτ a).map_source hq
  have hs : ContinuousAt (localCoefficient τ hτ 6 a s.val) (chart τ hτ a q) :=
    (((s.property a) _ ht).differentiableAt ((chart τ hτ a).open_target.mem_nhds ht)).continuousAt
  have hc : ContinuousAt (localCoefficient τ hτ 3 a (thetaVector τ hτ 3 j).val)
      (chart τ hτ a q) :=
    ((((thetaVector τ hτ 3 j).property a) _ ht).differentiableAt
      ((chart τ hτ a).open_target.mem_nhds ht)).continuousAt
  have hn : localCoefficient τ hτ 3 a (thetaVector τ hτ 3 j).val (chart τ hτ a q) ≠ 0 := by
    rw [coefficient_formula,section_projection τ hτ a q hq]
    exact mul_ne_zero (pow_ne_zero _ (transition_nonzero τ hτ _ _ _)) hj
  have hcomp : ContinuousAt
      (fun r : Base τ => localCoefficient τ hτ 6 a s.val (chart τ hτ a r) /
        (localCoefficient τ hτ 3 a (thetaVector τ hτ 3 j).val (chart τ hτ a r))^2) q :=
    ContinuousAt.comp (f := (chart τ hτ a : Base τ → ComplexVectors))
      (g := fun z => localCoefficient τ hτ 6 a s.val z /
        (localCoefficient τ hτ 3 a (thetaVector τ hτ 3 j).val z)^2)
      (x := q) (hs.div (hc.pow 2) (pow_ne_zero 2 hn)) ((chart τ hτ a).continuousAt hq)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(chart τ hτ a).open_source.mem_nhds hq] with r hr
  exact local_ratio τ hτ j s a r hr

/-- A genuine scalar function on the ENTIRE independent affine candidate,
not on a denominator-restricted primitive chart. -/
@[expose] def candidateRatio (j : Label 3) (s : homogeneous τ hτ 6)
    (w : Locus τ hτ j) : ℂ := baseRatio τ hτ j s (sourcePoint τ hτ j w)

lemma candidate_denominator_ne_zero (j : Label 3) (w : Locus τ hτ j) :
    (thetaVector τ hτ 3 j).val (sourcePoint τ hτ j w) ≠ 0 := by
  have hmem : projectiveMap τ hτ 1 (sourcePoint τ hτ j w) ∈ domain (Label 3) j := by
    rw [sourcePoint_image]
    exact (ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j).map_target (mem_univ w.val)
  exact (mk_mem_domain (Label 3) j _ _).mp hmem

theorem candidateRatio_continuous (j : Label 3) (s : homogeneous τ hτ 6) :
    Continuous (candidateRatio τ hτ j s) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  exact ContinuousAt.comp (f := sourcePoint τ hτ j) (g := baseRatio τ hτ j s)
    (x := w) (baseRatio_continuousAt τ hτ j s _ (candidate_denominator_ne_zero τ hτ j w))
    (sourcePoint_continuous τ hτ j).continuousAt
end PELOriginalSexticChartRatios318
