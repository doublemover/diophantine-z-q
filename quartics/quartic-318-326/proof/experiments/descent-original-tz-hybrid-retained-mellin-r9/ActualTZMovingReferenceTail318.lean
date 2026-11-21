module
public import ActualTZPositiveEulerMajorant318
public section
noncomputable section
namespace ActualTZMovingReferenceTail318
open ActualTZPositiveEulerMajorant318

/-- Strictly-larger-than-N integer envelope for omitted reference
primes, specialized to the actual movable σ=1/L. If the prime
universe is primesBelow (N+1), this contains exactly its omitted
range, including a prime at N+1. -/
theorem raw_tail (L : ℝ) (hL : 0<L) (N : ℕ) (hN : Real.exp (L^2)≤(N:ℝ)) :
    (∑' n : ℕ,((n+N+1:ℕ):ℝ)^((-1:ℝ)-(1/L))) ≤ L*Real.exp (-L) := by
  have hNposR := (Real.exp_pos (L^2)).trans_le hN
  have hNpos : 0<N := by exact_mod_cast hNposR
  have hdiv : 0<(1:ℝ)/L := by positivity
  have hp := Real.rpow_le_rpow_of_nonpos (Real.exp_pos (L^2)) hN
    (neg_nonpos.mpr hdiv.le)
  have he : L^2*(-(1/L:ℝ))= -L := by field_simp [hL.ne'] <;> ring
  have ht : (N:ℝ)^(-(1/L:ℝ))≤Real.exp (-L) := by
    exact hp.trans_eq (by rw [←Real.exp_mul,he])
  have H := (integer_tail (1/L) hdiv N hNpos).trans (div_le_div_of_nonneg_right ht hdiv.le)
  have hr : Real.exp (-L)/(1/L)=L*Real.exp (-L) := by
    rw [one_div,div_eq_mul_inv,inv_inv,mul_comm]
  rw [hr] at H
  -- Keep the exponent as -1-(1/L), not the parser's (-1-1)/L.
  simpa only [sub_eq_add_neg] using H

end ActualTZMovingReferenceTail318
