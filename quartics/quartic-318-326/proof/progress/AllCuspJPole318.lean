module
public import AllCuspJHolomorphic318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 AllCuspCharts318 QuotientJ318 AllCuspQJ318 AllCuspJ318
namespace AllCuspJPole318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def numerator (w:ℕ) (q:ℂ) : ℂ:=ActualQJ318.G (q^w)
@[expose] def localJ (w:ℕ) (q:ℂ) : ℂ:=numerator w q/q^w

theorem numerator_zero (w:ℕ) (hw:0<w) : numerator w 0=1 := by
  simp only [numerator,zero_pow (Nat.ne_of_gt hw),ActualQJ318.G_zero]

theorem numerator_analytic (w:ℕ) (hw:0<w) : AnalyticAt ℂ (numerator w) 0 := by
  have hp:AnalyticAt ℂ (fun q:ℂ=>q^w) 0:=analyticAt_id.pow w
  have hg:AnalyticAt ℂ ActualQJ318.G ((0:ℂ)^w):=by
    rw [zero_pow (Nat.ne_of_gt hw)]
    exact FilledJPole318.numerator_analytic
  exact AnalyticAt.comp (f := fun q : ℂ => q^w) hg hp

theorem local_meromorphic (w:ℕ) (hw:0<w) : MeromorphicAt (localJ w) 0 :=
  (numerator_analytic w hw).meromorphicAt.div ((MeromorphicAt.id 0).pow w)

/-- The actual width-w local j expression has pole order exactly minus w. -/
theorem local_order (w:ℕ) (hw:0<w) : meromorphicOrderAt (localJ w) 0=(-(w:ℤ)) := by
  apply (meromorphicOrderAt_eq_int_iff (local_meromorphic w hw)).mpr
  refine ⟨numerator w,numerator_analytic w hw,by rw [numerator_zero w hw];norm_num,?_⟩
  filter_upwards [] with q
  simp only [localJ,sub_zero,zpow_neg,zpow_natCast,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem coordinate_germ (N:ℕ) (hN:5≤N) (c:End N) :
    (fun q:ℂ=>filledJ N hN ((newChart N hN c).symm q)) =ᶠ[𝓝 0]
      localJ (natWidth N hN c) := by
  filter_upwards [(disc_open N hN c).mem_nhds (zeroPoint N hN c).property] with q hq
  exact filledJ_coordinate N hN c q hq

/-- The genuine global j-function is meromorphic at every actual cusp in its
registered genuine complex chart. -/
theorem cusp_meromorphic (N:ℕ) (hN:5≤N) (c:End N) :
    MeromorphicAt (fun q:ℂ=>filledJ N hN ((newChart N hN c).symm q)) 0 :=
  (local_meromorphic (natWidth N hN c) (natWidth_pos N hN c)).congr
    ((coordinate_germ N hN c).filter_mono nhdsWithin_le_nhds).symm

theorem cusp_order (N:ℕ) (hN:5≤N) (c:End N) :
    meromorphicOrderAt (fun q:ℂ=>filledJ N hN ((newChart N hN c).symm q)) 0=(-(natWidth N hN c:ℤ)) := by
  rw [meromorphicOrderAt_congr ((coordinate_germ N hN c).filter_mono nhdsWithin_le_nhds)]
  exact local_order _ (natWidth_pos N hN c)

theorem cusp_coordinate_zero (N:ℕ) (hN:5≤N) (c:End N) : newChart N hN c (cusp N hN c)=0 :=
  new_apply N hN c (zeroPoint N hN c)

/-- The reciprocal is genuinely holomorphic at every cusp. -/
theorem reciprocal_analytic (w:ℕ) (hw:0<w) : AnalyticAt ℂ (fun q:ℂ=>q^w/numerator w q) 0 :=
  (analyticAt_id.pow w).div (numerator_analytic w hw) (by rw [numerator_zero w hw];norm_num)

theorem reciprocal_germ (N:ℕ) (hN:5≤N) (c:End N) :
    (fun q:ℂ=>(filledJ N hN ((newChart N hN c).symm q))⁻¹) =ᶠ[𝓝 0]
      (fun q:ℂ=>q^natWidth N hN c/numerator (natWidth N hN c) q) := by
  filter_upwards [coordinate_germ N hN c] with q hq
  simp only [hq,localJ,inv_div]

theorem cusp_reciprocal_analytic (N:ℕ) (hN:5≤N) (c:End N) :
    AnalyticAt ℂ (fun q:ℂ=>(filledJ N hN ((newChart N hN c).symm q))⁻¹) 0 :=
  (reciprocal_analytic _ (natWidth_pos N hN c)).congr (reciprocal_germ N hN c).symm

/-- The reciprocal has zero order exactly the actual cusp width. -/
theorem cusp_reciprocal_order (N:ℕ) (hN:5≤N) (c:End N) :
    meromorphicOrderAt (fun q:ℂ=>(filledJ N hN ((newChart N hN c).symm q))⁻¹) 0 =
      (natWidth N hN c:ℤ) := by
  change meromorphicOrderAt ((fun q:ℂ=>filledJ N hN ((newChart N hN c).symm q))⁻¹) 0 = _
  rw [meromorphicOrderAt_inv,cusp_order]
  simp

end AllCuspJPole318
