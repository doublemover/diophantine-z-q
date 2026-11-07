module
public import PeriodEisenstein318
public import ModularWeierstrass318
public section
noncomputable section
namespace LatticeInvariants318
open PeriodEisenstein318
set_option maxHeartbeats 0

theorem bernoulli_six : bernoulli 6 = (1/42 : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 6 ≠ 1)]
  have hb5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose]
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, hb5, Nat.choose]

theorem zeta_six : riemannZeta 6 = (Real.pi : ℂ)^6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [bernoulli_six] at h
  rw [h]
  ring

theorem G_four (tau : UpperHalfPlane) :
    (periods tau).G 4 = (Real.pi : ℂ)^4 / 45 * ModularForm.E₄ tau := by
  rw [G_eq_normalized tau 4 (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  rw [riemannZeta_four]
  ring

theorem G_six (tau : UpperHalfPlane) :
    (periods tau).G 6 = 2*(Real.pi : ℂ)^6 / 945 * ModularForm.E₆ tau := by
  rw [G_eq_normalized tau 6 (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  rw [zeta_six]
  ring

theorem g2_normalization (tau : UpperHalfPlane) :
    (periods tau).g₂ = 4*(Real.pi : ℂ)^4 / 3 * ModularForm.E₄ tau := by
  rw [PeriodPair.g₂, G_four]
  ring

theorem g3_normalization (tau : UpperHalfPlane) :
    (periods tau).g₃ = 8*(Real.pi : ℂ)^6 / 27 * ModularForm.E₆ tau := by
  rw [PeriodPair.g₃, G_six]
  ring

/-- Actual normalized Weierstrass coordinates constructed from the genuine
lattice ℘-function and its genuine derivative. -/
@[expose] def xCoord (tau : UpperHalfPlane) (z : ℂ) : ℂ :=
  (periods tau).weierstrassP z / (2*(Real.pi : ℂ))^2

@[expose] def yCoord (tau : UpperHalfPlane) (z : ℂ) : ℂ :=
  (periods tau).derivWeierstrassP z / (2*(2*(Real.pi : ℂ))^3)

/-- The actual ℘ coordinates satisfy the normalized model's actual cubic,
with neither a lattice-invariant normalization nor a j equality assumed. -/
theorem normalized_weierstrass_equation (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    yCoord tau z ^ 2 = xCoord tau z ^ 3 -
      ModularForm.E₄ tau / 48 * xCoord tau z - ModularForm.E₆ tau / 864 := by
  have h := (periods tau).derivWeierstrassP_sq z hz
  rw [g2_normalization, g3_normalization] at h
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold xCoord yCoord
  field_simp [hp]
  linear_combination 41472*h

end LatticeInvariants318
