module
public import FilledJ318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 FilledCuspCharts318 FilledJ318
namespace FilledJPole318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem numerator_analytic : AnalyticAt ℂ ActualQJ318.G 0 :=
  ActualQJ318.G_holomorphic.analyticAt (Metric.ball_mem_nhds 0 (by norm_num))

theorem local_meromorphic : MeromorphicAt (fun q:ℂ=>ActualQJ318.G q/q) 0 :=
  numerator_analytic.meromorphicAt.div (MeromorphicAt.id 0)

theorem local_order : meromorphicOrderAt (fun q:ℂ=>ActualQJ318.G q/q) 0=(-1:ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff local_meromorphic).mpr
  refine ⟨ActualQJ318.G,numerator_analytic,by simp [ActualQJ318.G_zero],?_⟩
  filter_upwards [] with q
  simp [zpow_neg_one,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem coordinate_germ (N:ℕ) :
    (fun q:ℂ=>filledJ N ((newChart N).symm q)) =ᶠ[𝓝 0]
      (fun q:ℂ=>ActualQJ318.G q/q) := by
  filter_upwards [disc.isOpen.mem_nhds zeroPoint.property] with q hq
  exact filledJ_coordinate N q hq

/-- The actual global filled function is meromorphic in its genuine cusp chart. -/
theorem cusp_meromorphic (N:ℕ) :
    MeromorphicAt (fun q:ℂ=>filledJ N ((newChart N).symm q)) 0 :=
  local_meromorphic.congr ((coordinate_germ N).filter_mono nhdsWithin_le_nhds).symm

/-- Its pole order is exactly one, not just bounded by a supplied pole assumption. -/
theorem cusp_order (N:ℕ) :
    meromorphicOrderAt (fun q:ℂ=>filledJ N ((newChart N).symm q)) 0=(-1:ℤ) := by
  rw [meromorphicOrderAt_congr ((coordinate_germ N).filter_mono nhdsWithin_le_nhds)]
  exact local_order

theorem cusp_coordinate_zero (N:ℕ) : newChart N (cusp N)=0 := new_apply N zeroPoint

theorem reciprocal_coordinate_germ (N:ℕ) :
    (fun q:ℂ=>(filledJ N ((newChart N).symm q))⁻¹) =ᶠ[𝓝 0]
      ActualJCusp318.reciprocalGerm := by
  filter_upwards [coordinate_germ N] with q hq
  simp only [hq,ActualJCusp318.reciprocalGerm,inv_div]

/-- The reciprocal extends holomorphically with derivative one at the new cusp. -/
theorem reciprocal_derivative (N:ℕ) :
    HasDerivAt (fun q:ℂ=>(filledJ N ((newChart N).symm q))⁻¹) 1 0 := by
  exact ActualJCusp318.reciprocalGerm_hasDerivAt.congr_of_eventuallyEq
    (reciprocal_coordinate_germ N)

end FilledJPole318
