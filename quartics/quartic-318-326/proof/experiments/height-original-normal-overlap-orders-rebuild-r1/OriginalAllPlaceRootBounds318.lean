module
public import OriginalAllPlaceNormalizedData318
public section
noncomputable section
namespace OriginalAllPlaceRootBounds318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open ActualFinitePlaceIntegers318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : Data c t w)

/-- The actual signed normalized roots descend to the SAME valuation ring
when t is integral, without a good-prime or invertible discriminant premise. -/
theorem finite_coordinates (ht : w (t : K c t) ≤ 1) :
    ∃ (T : V c t w) (z : Fin 4 → V c t w),
      algebraMap (V c t w) (K c t) T = (t : K c t) ∧
      (∀ i, algebraMap (V c t w) (K c t) (z i) = D.normalizedRoots i) ∧
      ∀ i, (z i)^2 = D.coefficients i *
        (T - IntegralSourceBranches318.contacts (V c t w) i) := by
  let T : V c t w := ⟨(t : K c t),(bounded_iff w _).mp ht⟩
  have hz (i : Fin 4) : ∃ z : V c t w,
      algebraMap (V c t w) (K c t) z = D.normalizedRoots i ∧
      z^2 = D.coefficients i * (T - IntegralSourceBranches318.contacts (V c t w) i) := by
    apply IntegralValuativeRootCoordinates318.square_preimage (V c t w) (K c t)
    rw [map_mul,map_sub]
    exact D.root_equation i
  choose z hz he using hz
  exact ⟨T,z,rfl,hz,he⟩

/-- At a nonintegral original coordinate, the literal reciprocal coordinate
and original signed roots divided by s_i*t are integral, on the SAME model. -/
theorem reciprocal_coordinates (ht : ¬ w (t : K c t) ≤ 1) :
    ∃ (T : V c t w) (z : Fin 4 → V c t w),
      (t : K c t) ≠ 0 ∧
      algebraMap (V c t w) (K c t) T = (t : K c t)⁻¹ ∧
      (∀ i, algebraMap (V c t w) (K c t) (z i) =
        roots c t i / (D.multiplier i * (t : K c t))) ∧
      (∀ i, (z i)^2 = D.coefficients i * T *
        (1 - IntegralSourceBranches318.contacts (V c t w) i * T)) ∧
      ∀ i, D.multiplier i * (t : K c t) *
        algebraMap (V c t w) (K c t) (z i) = roots c t i := by
  have ht0 : (t : K c t) ≠ 0 := by
    intro h
    exact ht (by simp only [h,map_zero]; norm_num)
  have hw : w ((t : K c t)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    have hp : 0 < w (t : K c t) := lt_trans zero_lt_one (lt_of_not_ge ht)
    have hi : 0 ≤ (w (t : K c t))⁻¹ := inv_nonneg.mpr hp.le
    have hm := inv_mul_cancel₀ hp.ne'
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge ht)) hi
    simpa only [mul_one,hm] using hmul
  let T : V c t w := ⟨(t : K c t)⁻¹,(bounded_iff w _).mp hw⟩
  obtain ⟨z,hz,he,hr⟩ := DVRNormalizedInfinityOrder318.integral_roots
    (V c t w) (K c t) D.coefficients
    (IntegralSourceBranches318.contacts (V c t w)) (fieldTwists c t)
    D.multiplier D.multiplier_ne D.original_coefficient (t : K c t) ht0 T rfl
    (roots c t) (original_root_equations c t w)
  exact ⟨T,z,ht0,rfl,hz,he,hr⟩

/-- Explicit local growth of EVERY specified original root at EVERY finite
place. The multiplier is exactly that defining the actual normalized model,
not a fresh scalar chosen merely to enforce a norm inequality. -/
theorem original_root_bound (i : Fin 4) :
    w (roots c t i) ≤ w (D.multiplier i) * max 1 (w (t : K c t)) := by
  by_cases ht : w (t : K c t) ≤ 1
  · obtain ⟨T,z,hT,hz,he⟩ := finite_coordinates c t w D ht
    have hb := integer_bound w (z i)
    rw [hz i] at hb
    change w (roots c t i / D.multiplier i) ≤ 1 at hb
    rw [map_div₀] at hb
    have h := (div_le_iff₀ (w.pos (D.multiplier_ne i))).mp hb
    simpa only [one_mul,max_eq_left ht,mul_one] using h
  · obtain ⟨T,z,ht0,hT,hz,he,hr⟩ := reciprocal_coordinates c t w D ht
    have hb := integer_bound w (z i)
    rw [hz i,map_div₀,map_mul] at hb
    have h := (div_le_iff₀ (mul_pos (w.pos (D.multiplier_ne i)) (w.pos ht0))).mp hb
    simpa only [one_mul,max_eq_right (le_of_lt (lt_of_not_ge ht))] using h
end OriginalAllPlaceRootBounds318
