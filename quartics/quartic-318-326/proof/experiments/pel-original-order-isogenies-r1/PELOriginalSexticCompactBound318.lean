module
public import PELOriginalSexticRatioClosedGraph318
public import Mathlib.Topology.Order.Compact
public section
noncomputable section
namespace PELOriginalSexticCompactBound318
open Set Filter Topology QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance sourceCompact : CompactSpace (Base τ) :=
  PELComplexPeriodSurface318.surface_compact τ hτ
local instance discretePeriods : DiscreteTopology (P τ) :=
  PELOriginalPeriodLattice318.original_discrete τ hτ

@[expose] def cubicSize (q : Base τ) : ℝ :=
  ∑ i : Label 3, ‖(thetaVector τ hτ 3 i).val q‖^2

lemma cubicSize_pos (q : Base τ) : 0 < cubicSize τ hτ q := by
  obtain ⟨i,hi⟩ := PELOriginalFiniteThetaGeneration318.finite_basepoint_free τ hτ 1 q
  apply Finset.sum_pos' (fun i _ => sq_nonneg _)
  refine ⟨i,Finset.mem_univ i,?_⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr hi)

/-- The numerator and denominator have the SAME norm transition weight6.
This scalar is independent of the selected local fiber gauge. -/
@[expose] def normalizedSize (s : homogeneous τ hτ 6) (q : Base τ) : ℝ :=
  ‖s.val q‖ / cubicSize τ hτ q

lemma local_size (s : homogeneous τ hτ 6) (a : ComplexVectors)
    (q : Base τ) (hq : q ∈ baseSet τ hτ a) :
    normalizedSize τ hτ s q =
      ‖localCoefficient τ hτ 6 a s.val (chart τ hτ a q)‖ /
        (∑ i : Label 3, ‖localCoefficient τ hτ 3 a
          (thetaVector τ hτ 3 i).val (chart τ hτ a q)‖^2) := by
  simp only [coefficient_formula,section_projection τ hτ a q hq,norm_mul,norm_pow,
    mul_pow,←pow_mul]
  rw [←Finset.mul_sum]
  exact (mul_div_mul_left _ _
    (pow_ne_zero 6 (norm_ne_zero_iff.mpr (transition_nonzero τ hτ _ _ _)))).symm

/-- Continuity is proved from actual local holomorphic section coefficients,
not from the generally discontinuous selected fiber-gauge values. -/
theorem normalizedSize_continuous (s : homogeneous τ hτ 6) :
    Continuous (normalizedSize τ hτ s) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let a := (core τ hτ).indexAt q
  have hq : q ∈ baseSet τ hτ a := (core τ hτ).mem_baseSet_at q
  have ht := (chart τ hτ a).map_source hq
  have hs : ContinuousAt (localCoefficient τ hτ 6 a s.val) (chart τ hτ a q) :=
    (((s.property a) _ ht).differentiableAt ((chart τ hτ a).open_target.mem_nhds ht)).continuousAt
  have hc (i : Label 3) : ContinuousAt
      (localCoefficient τ hτ 3 a (thetaVector τ hτ 3 i).val) (chart τ hτ a q) :=
    ((((thetaVector τ hτ 3 i).property a) _ ht).differentiableAt
      ((chart τ hτ a).open_target.mem_nhds ht)).continuousAt
  have hn : (∑ i : Label 3, ‖localCoefficient τ hτ 3 a
      (thetaVector τ hτ 3 i).val (chart τ hτ a q)‖^2) ≠ 0 := by
    simp only [coefficient_formula,section_projection τ hτ a q hq,norm_mul,norm_pow,
      mul_pow,←pow_mul]
    rw [←Finset.mul_sum]
    exact mul_ne_zero
      (pow_ne_zero 6 (norm_ne_zero_iff.mpr (transition_nonzero τ hτ _ _ _)))
      (ne_of_gt (cubicSize_pos τ hτ q))
  have hcont : ContinuousAt
      (fun r : Base τ => ‖localCoefficient τ hτ 6 a s.val (chart τ hτ a r)‖ /
        ∑ i : Label 3, ‖localCoefficient τ hτ 3 a
          (thetaVector τ hτ 3 i).val (chart τ hτ a r)‖^2) q :=
    ContinuousAt.comp (f := (chart τ hτ a : Base τ → ComplexVectors))
      (g := fun z => ‖localCoefficient τ hτ 6 a s.val z‖ /
        ∑ i : Label 3, ‖localCoefficient τ hτ 3 a (thetaVector τ hτ 3 i).val z‖^2)
      (x := q) (hs.norm.div (continuousAt_finset_sum _ (fun i _ => (hc i).norm.pow 2)) hn)
      ((chart τ hτ a).continuousAt hq)
  apply hcont.congr_of_eventuallyEq
  filter_upwards [(chart τ hτ a).open_source.mem_nhds hq] with r hr
  exact local_size τ hτ s a r hr

/-- Compactness of the ORIGINAL torus produces a uniform, gauge-correct
quadratic bound for EVERY actual full sextic section. No normal generation
or algebraic section identification is used. -/
theorem exists_bound (s : homogeneous τ hτ 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Base τ, ‖s.val q‖ ≤ C * cubicSize τ hτ q := by
  obtain ⟨C,hC⟩ := (isCompact_range (normalizedSize_continuous τ hτ s)).bddAbove
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro q
  have h : normalizedSize τ hτ s q ≤ max C 0 :=
    (hC (Set.mem_range_self q)).trans (le_max_left _ _)
  exact (div_le_iff₀ (cubicSize_pos τ hτ q)).mp h
end PELOriginalSexticCompactBound318
