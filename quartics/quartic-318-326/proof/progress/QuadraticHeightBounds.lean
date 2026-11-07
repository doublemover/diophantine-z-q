module
public import Mathlib.NumberTheory.MahlerMeasure
public import Mathlib.NumberTheory.Height.NumberField
public section
noncomputable section
namespace QuadraticHeightBounds
open Polynomial

lemma quadratic_coeff_bounds (p : ℤ[X]) (hp : p.natDegree = 2)
    (hm : (p.map (Int.castRingHom ℂ)).mahlerMeasure < 81) :
    |p.coeff 2| ≤ 81 ∧ |p.coeff 1| ≤ 162 ∧ |p.coeff 0| ≤ 81 := by
  have hd : (p.map (Int.castRingHom ℂ)).natDegree = 2 := by
    rw [Polynomial.natDegree_map_eq_of_injective (Int.cast_injective),hp]
  have h0 := (p.map (Int.castRingHom ℂ)).norm_coeff_le_choose_mul_mahlerMeasure 0
  have h1 := (p.map (Int.castRingHom ℂ)).norm_coeff_le_choose_mul_mahlerMeasure 1
  have h2 := (p.map (Int.castRingHom ℂ)).norm_coeff_le_choose_mul_mahlerMeasure 2
  rw [hd] at h0 h1 h2
  norm_num [Polynomial.coeff_map] at h0 h1 h2
  have hc0 : (|(p.coeff 0 : ℝ)|) ≤ 81 := by simpa using h0.trans hm.le
  have hc1 : (|(p.coeff 1 : ℝ)|) ≤ 162 := by
    have := h1.trans (mul_le_mul_of_nonneg_left hm.le (by norm_num : (0:ℝ)≤2))
    norm_num at this
    simpa using this
  have hc2 : (|(p.coeff 2 : ℝ)|) ≤ 81 := by simpa using h2.trans hm.le
  exact ⟨by exact_mod_cast hc2,by exact_mod_cast hc1,by exact_mod_cast hc0⟩

lemma mahler_lt_of_actual_height {F : Type*} [Field F] [CharZero F]
    (x : F) (p : ℤ[X])
    (hformula : (p.map (Int.castRingHom ℂ)).mahlerMeasure =
      Real.exp (2 * NumberField.absLogHeight₁ x))
    (hheight : NumberField.absLogHeight₁ x < Real.log 9) :
    (p.map (Int.castRingHom ℂ)).mahlerMeasure < 81 := by
  rw [hformula]
  have h := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hheight (by norm_num : (0:ℝ)<2))
  have he : Real.exp (2 * Real.log 9) = 81 := by
    rw [← Real.log_rpow (by norm_num : (0:ℝ)<9)]
    norm_num
    exact Real.exp_log (by norm_num)
  exact h.trans_eq he

lemma discriminant_bound (a b c : ℤ) (k : ℕ)
    (ha : 1 ≤ a) (hA : a ≤ 81) (hb : |b| ≤ 162) (hc : |c| ≤ 81)
    (hd : b^2-4*a*c=2*(k:ℤ)^2) : k ≤ 162 := by
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hs : b^2 ≤ 162^2 := by nlinarith [sq_nonneg (b-162),sq_nonneg (b+162)]
  have hac : -4*a*c ≤ 4*81*81 := by
    have := mul_le_mul_of_nonneg_left hc'.1 (by omega : 0≤a)
    nlinarith
  have hk : (k:ℤ) ≤ 162 := by nlinarith [sq_nonneg ((k:ℤ)-162)]
  exact_mod_cast hk

#print axioms quadratic_coeff_bounds
#print axioms mahler_lt_of_actual_height
#print axioms discriminant_bound
end QuadraticHeightBounds
