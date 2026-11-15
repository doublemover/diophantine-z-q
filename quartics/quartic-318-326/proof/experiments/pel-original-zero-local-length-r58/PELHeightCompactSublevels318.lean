module
public import PELDirichletHeight318
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public section
noncomputable section
namespace PELHeightCompactSublevels318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
set_option maxHeartbeats 1600000

theorem normSq_continuous : Continuous Complex.normSq := by
  simpa only [Complex.normSq_apply] using
    (Complex.continuous_re.mul Complex.continuous_re).add
      (Complex.continuous_im.mul Complex.continuous_im)

theorem height_continuous : Continuous height := by
  exact ((normSq_continuous.comp continuous_subtype_val).add continuous_const).div
    (Complex.continuous_im.comp continuous_subtype_val) (fun τ => τ.property.ne')

/-- A sublevel is bounded AWAY from the real boundary. Its compactness is
proved in the original upper-half-plane topology, not in an added compactification. -/
theorem sublevel_compact (C : ℝ) (hC : 0<C) :
    IsCompact {τ : HalfPlane | height τ≤C} := by
  let S : Set ℂ := {z | 1/C≤z.im ∧ Complex.normSq z+1≤C*z.im}
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le (normSq_continuous.add continuous_const)
        (continuous_const.mul Complex.continuous_im))
  have hbound : S⊆Metric.closedBall (0:ℂ) C := by
    intro z hz
    have hy : 0<z.im := lt_of_lt_of_le (div_pos zero_lt_one hC) hz.1
    have hyC : z.im≤C := by
      have h := hz.2
      rw [Complex.normSq_apply] at h
      by_contra hnot
      have hp := mul_pos hy (sub_pos.mpr (lt_of_not_ge hnot))
      nlinarith [sq_nonneg z.re]
    have hns : Complex.normSq z≤C^2 := by
      have hc := mul_le_mul_of_nonneg_left hyC hC.le
      nlinarith [hz.2]
    have hn : ‖z‖≤C := by nlinarith [Complex.sq_norm z,norm_nonneg z]
    simpa only [Metric.mem_closedBall,dist_zero_right] using hn
  have hcompact : IsCompact S :=
    (isCompact_closedBall (0:ℂ) C).of_isClosed_subset hclosed hbound
  apply Subtype.isCompact_iff.mpr
  convert hcompact using 1
  ext z
  constructor
  · rintro ⟨τ,hτ,rfl⟩
    have h := (div_le_iff₀ τ.property).mp hτ
    refine ⟨(div_le_iff₀ hC).mpr ?_,h⟩
    nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  · intro hz
    have hy : 0<z.im := lt_of_lt_of_le (div_pos zero_lt_one hC) hz.1
    exact ⟨⟨z,hy⟩,(div_le_iff₀ hy).mpr hz.2,rfl⟩
end PELHeightCompactSublevels318
