module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace UpperHalfPlanePowerRays318
open Complex
set_option maxHeartbeats 1800000

/-- For every putative boundary order at least two, there are TWO genuine
upper-half-plane rays whose n-th powers have opposite imaginary signs. -/
theorem opposite_power_rays (n : ℕ) (hn : 2≤n) :
    ∃ a b : ℂ,0<a.im ∧ 0<b.im ∧ a^n=I ∧ b^n= -I := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : n≠0 := by omega
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn0
  have hd : (0:ℝ)<2*n := by positivity
  let θ : ℝ := Real.pi/(2*n)
  let φ : ℝ := 3*Real.pi/(2*n)
  let a : ℂ := exp ((θ:ℂ)*I)
  let b : ℂ := exp ((φ:ℂ)*I)
  have hθ0 : 0<θ := div_pos Real.pi_pos hd
  have hφ0 : 0<φ := div_pos (by positivity) hd
  have hθπ : θ<Real.pi := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_pos]
  have hφπ : φ<Real.pi := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_pos]
  have hai : a.im=Real.sin θ := by
    dsimp [a]
    rw [←Complex.cos_add_sin_I]
    simp
  have hbi : b.im=Real.sin φ := by
    dsimp [b]
    rw [←Complex.cos_add_sin_I]
    simp
  refine ⟨a,b,by rw [hai]; exact Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ,
    by rw [hbi]; exact Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ,?_,?_⟩
  · dsimp [a]
    rw [←Complex.exp_nat_mul]
    have he : (n:ℂ)*((θ:ℂ)*I)=(Real.pi:ℂ)/2*I := by
      dsimp [θ]
      push_cast
      field_simp [hnC] <;> ring
    rw [he,Complex.exp_pi_div_two_mul_I]
  · dsimp [b]
    rw [←Complex.exp_nat_mul]
    have he : (n:ℂ)*((φ:ℂ)*I)=(Real.pi:ℂ)*I+(Real.pi:ℂ)/2*I := by
      dsimp [φ]
      push_cast
      field_simp [hnC] <;> ring
    rw [he,Complex.exp_add,Complex.exp_pi_mul_I,Complex.exp_pi_div_two_mul_I]
    ring
end UpperHalfPlanePowerRays318
