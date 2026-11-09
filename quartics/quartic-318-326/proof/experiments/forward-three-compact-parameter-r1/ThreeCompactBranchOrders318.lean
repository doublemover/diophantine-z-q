module
public import ThreeCompactParameter318
public import Mathlib.Analysis.Meromorphic.Order
public section
noncomputable section
open Filter Topology
namespace ThreeCompactBranchOrders318
open ThreeCompactParameter318
set_option maxHeartbeats 0

lemma J_meromorphic (t : ℂ) : MeromorphicAt J t := by
  unfold J
  fun_prop

lemma J_analytic {t : ℂ} (ht : t ≠ 0) : AnalyticAt ℂ J t := by
  unfold J
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact pow_ne_zero _ ht

lemma X_analytic {t : ℂ} (ht : D t ≠ 0) : AnalyticAt ℂ X t := by
  unfold X
  apply AnalyticAt.div
  · fun_prop
  · unfold D; fun_prop
  · exact ht

/-- The actual local order at the simple zero in the rational parameter. -/
theorem order_at_simple_zero : meromorphicOrderAt J (-27)=1 := by
  apply (meromorphicOrderAt_eq_int_iff (J_meromorphic (-27))).mpr
  refine ⟨fun t : ℂ => (t+243)^3/t^3, ?_, ?_, ?_⟩
  · apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · norm_num
  · norm_num
  · exact Filter.Eventually.of_forall (fun t => by simp [J,smul_eq_mul]; ring)

/-- The actual local order at the ramified zero, without a cardinality argument. -/
theorem order_at_triple_zero : meromorphicOrderAt J (-243)=3 := by
  apply (meromorphicOrderAt_eq_int_iff (J_meromorphic (-243))).mpr
  refine ⟨fun t : ℂ => (t+27)/t^3, ?_, ?_, ?_⟩
  · apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · norm_num
  · norm_num
  · exact Filter.Eventually.of_forall (fun t => by simp [J,smul_eq_mul]; ring)

/-- The finite cusp has pole order three for this exact rational j map. -/
theorem order_at_zero_cusp : meromorphicOrderAt J 0 = -3 := by
  apply (meromorphicOrderAt_eq_int_iff (J_meromorphic 0)).mpr
  refine ⟨fun t : ℂ => (t+27)*(t+243)^3, by fun_prop, by norm_num, ?_⟩
  exact Filter.Eventually.of_forall (fun t => by simp [J,smul_eq_mul,div_eq_mul_inv]; ring)

@[expose] def infinityExpression (s : ℂ) : ℂ := (1+27*s)*(1+243*s)^3/s

lemma infinity_expression_eq {s : ℂ} (hs : s ≠ 0) :
    J s⁻¹=infinityExpression s := J_reciprocal s hs

/-- Pole order one in the reciprocal projective chart. -/
theorem order_at_infinity_cusp : meromorphicOrderAt infinityExpression 0 = -1 := by
  have hm : MeromorphicAt infinityExpression 0 := by unfold infinityExpression; fun_prop
  apply (meromorphicOrderAt_eq_int_iff hm).mpr
  refine ⟨fun s : ℂ => (1+27*s)*(1+243*s)^3, by fun_prop, by norm_num, ?_⟩
  exact Filter.Eventually.of_forall (fun s => by
    simp [infinityExpression,smul_eq_mul,div_eq_mul_inv]; ring)

lemma D_root_ne_zero {r : ℂ} (hr : D r=0) : r ≠ 0 := by
  intro he
  subst r
  norm_num [D] at hr

lemma D_root_simple {r : ℂ} (hr : D r=0) : 2*r-486 ≠ 0 := by
  intro he
  have h243 : r=243 := by linear_combination (1/2:ℂ)*he
  rw [h243] at hr
  norm_num [D] at hr

lemma D_root_factor {r : ℂ} (hr : D r=0) (t : ℂ) :
    D t=(t-r)*(t+r-486) := by
  unfold D at *
  linear_combination hr

/-- Both roots of the original D-polynomial have exact j-1728 order two.
The statement covers every complex root without choosing its square root. -/
theorem order_at_1728 {r : ℂ} (hr : D r=0) :
    meromorphicOrderAt (fun t => J t-1728) r = 2 := by
  have hr0 := D_root_ne_zero hr
  have hm : MeromorphicAt (fun t => J t-1728) r :=
    (J_meromorphic r).sub (by fun_prop)
  apply (meromorphicOrderAt_eq_int_iff hm).mpr
  refine ⟨fun t : ℂ => (t+r-486)^2/t^3, ?_, ?_, ?_⟩
  · apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ hr0
  · apply div_ne_zero
    · apply pow_ne_zero
      convert D_root_simple hr using 1
      ring
    · exact pow_ne_zero _ hr0
  · have hev : ∀ᶠ t in 𝓝[≠] r, t ≠ (0:ℂ) :=
      eventually_ne_nhdsWithin hr0
    filter_upwards [hev] with t ht
    rw [J_sub_1728 t ht,D_root_factor hr t]
    norm_num only [zpow_ofNat, zpow_two, smul_eq_mul]
    ring

/-- Complete finite zero fiber, including the two distinct branches. -/
theorem zero_fiber {t : ℂ} (ht : t ≠ 0) :
    J t=0 ↔ t = -27 ∨ t = -243 := by
  simp [J,ht,add_eq_zero_iff_eq_neg]

/-- Complete finite 1728 fiber, in the same original rational map. -/
theorem elliptic_fiber {t : ℂ} (ht : t ≠ 0) :
    J t=1728 ↔ D t=0 := by
  exact not_iff_not.mp (J_ne_1728_iff ht)

@[expose] def homogeneousNumerator (u v : ℂ) : ℂ := (u+27*v)*(u+243*v)^3
@[expose] def homogeneousDenominator (u v : ℂ) : ℂ := u^3*v

/-- The homogeneous degree-four pair has no projective base point. This
does not, by itself, register a Scheme or projective analytic morphism. -/
theorem no_projective_basepoint {u v : ℂ} (huv : u ≠ 0 ∨ v ≠ 0) :
    homogeneousNumerator u v ≠ 0 ∨ homogeneousDenominator u v ≠ 0 := by
  by_cases hu : u=0
  · have hv := huv.resolve_left (not_not.mpr hu)
    left
    simp [homogeneousNumerator,hu,hv]
  · by_cases hv : v=0
    · left
      simp [homogeneousNumerator,hv,hu]
    · right
      exact mul_ne_zero (pow_ne_zero _ hu) hv

lemma homogeneous_elliptic_identity (u v : ℂ) :
    homogeneousNumerator u v-1728*homogeneousDenominator u v=
      (u^2-486*u*v-19683*v^2)^2 := by
  unfold homogeneousNumerator homogeneousDenominator
  ring

lemma homogeneous_affine_identity (t : ℂ) :
    homogeneousNumerator t 1/homogeneousDenominator t 1=J t := by
  simp [homogeneousNumerator,homogeneousDenominator,J]

end ThreeCompactBranchOrders318
