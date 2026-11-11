module
public import LiteralContactMetricCharts318
public section
noncomputable section
namespace LiteralChartMetricFunctions318
open Set Filter LiteralMetricExtension318 SourceMetricCharts318
open MetricSmoothExtension318 MetricPullback318 LiteralContactMetricCharts318
open scoped Topology ContDiff

@[expose] def value : Chart → ℂ → ℝ
  | .regular t _ => fun z => sourceCoefficient contacts (t+z)
  | .finiteBranch i => branchCoefficient (fun j : {j : Fin 4 // j≠i} => contacts i-contacts j)
  | .infinity => infinityCoefficient contacts
lemma value_real (k : Chart) (w : ℝ×ℝ) :
    value k (QuadraticOrigin318.complexCoord w)=k.coefficient w := by cases k <;> rfl
lemma value_positive (k : Chart) : 0<value k 0 := by
  simpa only [←value_real,QuadraticOrigin318.complexCoord,Complex.ofReal_zero,zero_mul,add_zero]
    using k.positive
lemma value_continuous (k : Chart) : ContinuousAt (value k) 0 := by
  cases k with
  | regular t ht =>
    have hn (i : Fin 4) : ContDiffAt ℝ ∞ (fun z : ℂ => ‖t+z-contacts i‖) 0 := by
      apply ContDiffAt.norm (𝕜:=ℂ)
      · fun_prop
      · simpa only [add_zero] using sub_ne_zero.mpr (ht i)
    have hs := ContDiffAt.sum (s:=Finset.univ) (fun i _ => hn i)
    have hp := contDiffAt_prod (t:=Finset.univ) (fun i _ => hn i)
    have hd : (∏ i : Fin 4,‖t+(0:ℂ)-contacts i‖)≠0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      simpa only [add_zero] using norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ht i))
    exact ((contDiffAt_const.add hs).div hp hd).continuousAt
  | finiteBranch i => exact (finite_branch_extension i).1.continuousAt
  | infinity => exact (infinity_extension).1.continuousAt

lemma coordinate_differentiable (k : Chart) (z : ℂ) (hz : z≠0) :
    DifferentiableAt ℂ (coordinate k) z := by
  cases k with
  | regular t ht => exact differentiableAt_const.add differentiableAt_id
  | finiteBranch i => exact differentiableAt_const.add (differentiableAt_id.pow 2)
  | infinity => exact differentiableAt_const.div (differentiableAt_id.pow 2) (pow_ne_zero 2 hz)

/-- Exact actual pullback by the prescribed quotient coordinate, with
all ramification derivatives and the infinity exponent retained. -/
lemma value_pullback (k : Chart) (z : ℂ) (hz : z≠0) :
    value k z=sourceCoefficient contacts (coordinate k z)*‖deriv (coordinate k) z‖^2 := by
  cases k with
  | regular t ht =>
    have hd : deriv (fun w : ℂ => t+w) z=1 := by
      simpa only [zero_add] using ((hasDerivAt_const z t).add (hasDerivAt_id z)).deriv
    simp only [value,coordinate,hd,norm_one,one_pow,mul_one]
  | finiteBranch i => exact (branch_actual_pullback contacts i z hz).symm
  | infinity => exact (MetricPullback318.infinity_actual_pullback contacts z hz).symm
end LiteralChartMetricFunctions318
