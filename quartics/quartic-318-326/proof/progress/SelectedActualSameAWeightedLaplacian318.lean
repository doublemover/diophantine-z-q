module
public import GradientNorm318
public import SelectedActualSameACurvature64

/-! Actual ordinary curvature of the weighted metric. Compute the
Laplacian of the literal coefficient, not a positivity assumption on a
supplied curvature function. The four-index cross terms retain their
own contact gaps rather than bounding the total gradient by 16. -/
public section
noncomputable section
open Filter Finset Set CompactMetricComparison318 ConformalCurvature318
open DistanceLaplacian318 FiniteLaplacian318
open scoped Topology
namespace SelectedActualSameAWeightedLaplacian318

def weight : Fin 4 → ℝ := ![1,1,1/7,1/80]
def mark : Fin 4 → ℝ := ![0,32,-343,76832]
def total (x y : Fin 4 → ℝ) (v : ℝ×ℝ) : ℝ :=
  960 + ∑ i, weight i * translated (x i) (y i) v
def metric (x y : Fin 4 → ℝ) (v : ℝ×ℝ) : ℝ :=
  total x y v / ContactCurvature318.product x y v

private theorem wpos (i : Fin 4) : 0 ≤ weight i := by fin_cases i <;> norm_num [weight]
theorem total_pos (x y : Fin 4 → ℝ) (v : ℝ×ℝ) : 0 < total x y v := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 4)))
    (fun i _ => mul_nonneg (wpos i) (Real.sqrt_nonneg ((x i + v.1)^2+(y i+v.2)^2)))
  change 0 < 960 + ∑ i, weight i * translated (x i) (y i) v
  change 0 ≤ ∑ i, weight i * translated (x i) (y i) v at h
  linarith

theorem weighted_C2 (x y : Fin 4 → ℝ) (h : ∀ i,0 < (x i)^2+(y i)^2) :
    AxisC2 (total x y) := by
  constructor
  · exact contDiffAt_const.add (ContDiffAt.sum (fun i _ =>
      contDiffAt_const.mul (translated_axisC2 _ _ (h i)).1))
  · exact contDiffAt_const.add (ContDiffAt.sum (fun i _ =>
      contDiffAt_const.mul (translated_axisC2 _ _ (h i)).2))

theorem metric_C2 (x y : Fin 4 → ℝ) (h : ∀ i,0 < (x i)^2+(y i)^2) :
    AxisC2 (metric x y) := by
  have hp : ContactCurvature318.product x y (0,0) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simpa [translated] using (radius_pos (h i)).ne'
  exact ⟨(weighted_C2 x y h).1.div
      (contDiffAt_prod (fun i _ => (translated_axisC2 _ _ (h i)).1)) hp,
    (weighted_C2 x y h).2.div
      (contDiffAt_prod (fun i _ => (translated_axisC2 _ _ (h i)).2)) hp⟩

private theorem lap_const_mul (c : ℝ) (f : ℝ×ℝ → ℝ) :
    laplacianAtOrigin (fun z => c * f z) = c * laplacianAtOrigin f := by
  simp only [laplacianAtOrigin,deriv_const_mul_field',deriv_const_mul_field,mul_add]

private theorem weighted_lap (x y : Fin 4 → ℝ) (h : ∀ i,0 < (x i)^2+(y i)^2) :
    laplacianAtOrigin (total x y) = ∑ i, weight i * (radius (x i) (y i))⁻¹ := by
  unfold total
  rw [laplacian_const_add,laplacian_sum _ (fun i => ⟨
    contDiffAt_const.mul (translated_axisC2 _ _ (h i)).1,
    contDiffAt_const.mul (translated_axisC2 _ _ (h i)).2⟩)]
  exact Finset.sum_congr rfl (fun i _ => (lap_const_mul _ _).trans
    (congrArg (weight i * ·) (laplacian_radius _ _ (h i))))

private theorem dx (x y : Fin 4 → ℝ) (h : ∀ i,0 < (x i)^2+(y i)^2) :
    deriv (fun t : ℝ => total x y (t,0)) 0 =
      ∑ i, weight i * (x i / radius (x i) (y i)) := by
  have hd := (HasDerivAt.sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_line (x i) (y i) 0 (by simpa using h i)).const_mul
      (weight i))).const_add 960
  simpa only [total,translated,add_zero,Finset.sum_apply] using hd.deriv

private theorem dy (x y : Fin 4 → ℝ) (h : ∀ i,0 < (x i)^2+(y i)^2) :
    deriv (fun t : ℝ => total x y (0,t)) 0 =
      ∑ i, weight i * (y i / radius (x i) (y i)) := by
  have he : (fun t:ℝ => total x y (0,t)) = (fun t => total y x (t,0)) := by
    funext t
    unfold total
    apply congrArg (960 + ·)
    apply Finset.sum_congr rfl
    intro i _
    simp only [translated,add_zero]
    rw [radius_symm]
  rw [he,dx y x (fun i => by linarith [h i])]
  exact Finset.sum_congr rfl (fun i _ => by rw [radius_symm (y i) (x i)])

theorem negative_curvature (x y : Fin 4 → ℝ) (h : ∀ i,0 < (x i)^2+(y i)^2) :
    -curvature (metric x y) =
      (∏ i,radius (x i) (y i))/(2*(total x y (0,0))^3) *
      (total x y (0,0) * (∑ i, weight i*(radius (x i) (y i))⁻¹) -
        ((∑ i,weight i*(x i / radius (x i) (y i)))^2 +
         (∑ i,weight i*(y i / radius (x i) (y i)))^2)) := by
  have near : ∀ᶠ v:ℝ×ℝ in 𝓝 (0,0), ∀ i,0 < translated (x i) (y i) v := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (translated (x i) (y i)) (0,0) := by
      unfold translated radius
      fun_prop
    exact hc.eventually (eventually_gt_nhds (by simpa [translated] using radius_pos (h i)))
  have he : (fun v => Real.log (metric x y v)) =ᶠ[𝓝 (0,0)]
      (fun v => Real.log (total x y v) - ∑ i,Real.log (translated (x i) (y i) v)) := by
    filter_upwards [near] with v hv
    rw [metric, ContactCurvature318.product,
      Real.log_div (total_pos x y v).ne'
        (Finset.prod_ne_zero_iff.mpr (fun i _ => (hv i).ne')),
      Real.log_prod (fun i _ => (hv i).ne')]
  have hl (i : Fin 4) : AxisC2 (fun v => Real.log (translated (x i) (y i) v)) :=
    ⟨((translated_axisC2 _ _ (h i)).1).log (by simpa [translated] using (radius_pos (h i)).ne'),
     ((translated_axisC2 _ _ (h i)).2).log (by simpa [translated] using (radius_pos (h i)).ne')⟩
  rw [curvature,laplacian_congr he, laplacian_sub _ _
    ⟨((weighted_C2 x y h).1).log (total_pos x y (0,0)).ne',
     ((weighted_C2 x y h).2).log (total_pos x y (0,0)).ne'⟩
    ⟨ContDiffAt.sum (fun i _ => (hl i).1),ContDiffAt.sum (fun i _ => (hl i).2)⟩,
    laplacian_sum _ hl]
  simp_rw [laplacian_log_radius _ _ (h _)]
  rw [Finset.sum_const_zero,sub_zero,laplacian_log _ (weighted_C2 x y h) (total_pos x y _).ne',
    weighted_lap x y h,gradientSq,dx x y h,dy x y h]
  have ht := (total_pos x y (0,0)).ne'
  have hp : (∏ i,radius (x i) (y i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (radius_pos (h i)).ne')
  simp only [metric,ContactCurvature318.product,translated,add_zero]
  field_simp [ht,hp]

/-- The exact diagonal cancellation for one normalized radial direction. -/
private theorem diagonal (x y : ℝ) (hr : 0 < x^2+y^2) :
    radius x y * (radius x y)⁻¹ -
      ((x / radius x y)^2+(y / radius x y)^2) = 0 := by
  have hn := (radius_pos hr).ne'
  rw [mul_inv_cancel₀ hn]
  field_simp [hn]
  nlinarith only [radius_sq x y]

/-- Pair identity retains the *square* of the true gap; y is the same
imaginary part because all four marked contact parameters are real. -/
private theorem pair (x X y : ℝ) (h : 0<x^2+y^2) (H : 0<X^2+y^2) :
    radius x y * (radius X y)⁻¹ + radius X y * (radius x y)⁻¹ -
      2*((x / radius x y)*(X / radius X y)+(y / radius x y)*(y / radius X y)) =
        (x-X)^2 / (radius x y * radius X y) := by
  have hr := (radius_pos h).ne'
  have hR := (radius_pos H).ne'
  field_simp [hr,hR]
  nlinarith only [radius_sq x y,radius_sq X y]

abbrev rad (x : Fin 4 → ℝ) (y : ℝ) (i : Fin 4) := radius (x i) y
private def diag (x : Fin 4 → ℝ) (y : ℝ) (i : Fin 4) :=
  rad x y i * (rad x y i)⁻¹ - ((x i/rad x y i)^2 + (y/rad x y i)^2)
private def mixed (x : Fin 4 → ℝ) (y : ℝ) (i j : Fin 4) :=
  rad x y i * (rad x y j)⁻¹ + rad x y j * (rad x y i)⁻¹ -
    2*((x i/rad x y i)*(x j/rad x y j)+(y/rad x y i)*(y/rad x y j))
private def spread (x : Fin 4 → ℝ) (y : ℝ) :=
  total x (fun _ => y) (0,0) * (∑ i,weight i*(rad x y i)⁻¹) -
    ((∑ i,weight i*(x i/rad x y i))^2+(∑ i,weight i*(y/rad x y i))^2)

private theorem expand_spread (x : Fin 4 → ℝ) (y : ℝ) :
    spread x y = 960*(∑ i,weight i*(rad x y i)⁻¹) + (∑ i,weight i^2 * diag x y i) +
      mixed x y 0 1 + mixed x y 0 2/7 + mixed x y 0 3/80 +
      mixed x y 1 2/7 + mixed x y 1 3/80 + mixed x y 2 3/560 := by
  simp [spread,total,translated,Fin.sum_univ_four,weight,diag,mixed,rad,div_eq_mul_inv]
  ring

@[expose] def offset (z : ℂ) (i : Fin 4) := z.re - mark i
def Ordinary (z : ℂ) : Prop := ∀ i, 0 < (offset z i)^2+z.im^2
def actualCoefficient (z : ℂ) : ℝ×ℝ → ℝ := metric (offset z) (fun _ => z.im)

theorem ordinary_iff (z : ℂ) : Ordinary z ↔ ∀ i,z ≠ (mark i : ℂ) := by
  constructor
  · intro h i e
    have hp := h i
    rw [e] at hp
    simp [offset] at hp
  · intro h i
    have hp := norm_pos_iff.mpr (sub_ne_zero.mpr (h i))
    have hs := Complex.sq_norm (z-(mark i:ℂ))
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
      Complex.ofReal_im,sub_zero] at hs
    dsimp [offset]
    nlinarith

private theorem rad_at (z : ℂ) (i : Fin 4) :
    rad (offset z) z.im i = ‖z-(mark i:ℂ)‖ := by
  simpa [rad,offset] using radius_complex (z-(mark i:ℂ))

private theorem num_calculation (z : ℂ) (h : Ordinary z) :
    (∏ i,rad (offset z) z.im i)*spread (offset z) z.im =
      SelectedActualSameACurvature64.N
        (rad (offset z) z.im 0) (rad (offset z) z.im 1)
        (rad (offset z) z.im 2) (rad (offset z) z.im 3) := by
  let x := offset z
  let y := z.im
  have hd (i : Fin 4) : diag x y i = 0 := diagonal (x i) y (h i)
  have hm (i j : Fin 4) : mixed x y i j =
      (mark i-mark j)^2/(rad x y i * rad x y j) := by
    rw [show mixed x y i j=(x i-x j)^2/(rad x y i * rad x y j) from
      pair (x i) (x j) y (h i) (h j)]
    have he : (x i-x j)^2 = (mark i-mark j)^2 := by dsimp [x,offset];ring
    rw [he]
  have hn (i : Fin 4) : rad x y i ≠ 0 := (radius_pos (h i)).ne'
  change (∏ i,rad x y i)*spread x y = _
  rw [expand_spread]
  simp only [hd,mul_zero,Finset.sum_const_zero,add_zero,hm,Fin.sum_univ_four,Fin.prod_univ_four]
  change _ = SelectedActualSameACurvature64.N (rad x y 0) (rad x y 1) (rad x y 2) (rad x y 3)
  norm_num [SelectedActualSameACurvature64.N,SelectedActualSameACurvature64.cubic,
    SelectedActualSameACurvature64.cross,mark,weight]
  field_simp [hn 0,hn 1,hn 2,hn 3]
  ring

open SelectedActualSameACurvature64 (curvatureRatio metricU a b c d)

theorem weighted_total_at (z : ℂ) :
    total (offset z) (fun _ => z.im) (0,0) = metricU z := by
  simp only [total,translated,add_zero]
  change 960 + (∑ i, weight i * rad (offset z) z.im i) = metricU z
  rw [Fin.sum_univ_four,rad_at,rad_at,rad_at,rad_at]
  norm_num [weight,mark,metricU,SelectedActualSameACurvature64.U,a,b,c,d]
  ring

/-- Equality for the ordinary point of the original weighted test metric,
with all six distinct constants, no replacement by a weaker metric. -/
theorem curvature_is_ratio (z : ℂ) (h : Ordinary z) :
    -curvature (actualCoefficient z) = curvatureRatio z := by
  let x := offset z
  let y := z.im
  have hn := negative_curvature x (fun _ => y) h
  change -curvature (actualCoefficient z) =
    (∏ i,rad x y i)/(2*(total x (fun _ => y) (0,0))^3)*spread x y at hn
  rw [hn]
  rw [div_mul_eq_mul_div, num_calculation z h, weighted_total_at]
  change SelectedActualSameACurvature64.N
    (rad (offset z) z.im 0) (rad (offset z) z.im 1)
    (rad (offset z) z.im 2) (rad (offset z) z.im 3) / (2*(metricU z)^3) = curvatureRatio z
  rw [rad_at,rad_at,rad_at,rad_at,curvatureRatio]
  norm_num [mark,a,b,c,d]

theorem ordinary_curvature_le (z : ℂ) (h : Ordinary z) :
    curvature (actualCoefficient z) ≤ -64 := by
  have hh := SelectedActualSameACurvature64.curvatureRatio_at_least_64 z
  rw [← curvature_is_ratio z h] at hh
  linarith

end SelectedActualSameAWeightedLaplacian318
