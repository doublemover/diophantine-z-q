module
public import ActualTZPositiveEulerMajorant318
public section
noncomputable section
namespace ActualTZPrimeReciprocalPrefix318
open scoped BigOperators
open ActualTZPositiveEulerMajorant318

private theorem log_reciprocal_ge (u : ℝ) (h : u<1) :
    u≤Real.log ((1-u)⁻¹) := by
  rw [Real.log_inv]
  linarith only [Real.log_le_sub_one_of_pos (sub_pos.mpr h)]

private theorem log_reference (σ : ℝ) (hσ : 0<σ) (P : ℕ) :
    (∑ p∈Nat.primesBelow P,q σ p)≤Real.log (1+1/σ) := by
  have H (p : ℕ) (hp : p∈Nat.primesBelow P) : 0<(1-q σ p)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (q_bounds σ hσ (Nat.prime_of_mem_primesBelow hp)).2)
  calc
    _ ≤ ∑ p∈Nat.primesBelow P,Real.log ((1-q σ p)⁻¹) := by
      exact Finset.sum_le_sum fun p hp =>
        log_reciprocal_ge _ (q_bounds σ hσ (Nat.prime_of_mem_primesBelow hp)).2
    _ = Real.log (∏ p∈Nat.primesBelow P,(1-q σ p)⁻¹) := by
      exact (Real.log_prod (fun p hp => (H p hp).ne')).symm
    _ ≤ _ := Real.log_le_log (Finset.prod_pos H)
      ((reference_upper σ hσ P).trans (zeta_norm_upper σ hσ))

/-- Genuine prime reciprocal prefix, from the positive Euler ζ
series at σ=1/log p. No PNT, no abstract prime-independence input. -/
theorem prefix (P : ℕ) (hP : 2≤P) :
    (∑ p∈Nat.primesBelow P,1/(p:ℝ))≤Real.exp 1*Real.log (1+Real.log P) := by
  have hPR : (1:ℝ)<P := by exact_mod_cast (show 1<P by omega)
  have hlog : 0<Real.log P := Real.log_pos hPR
  let σ := (1:ℝ)/Real.log P
  have hσ : 0<σ := by dsimp only [σ]; positivity
  have hAtom (p : ℕ) (hp : p∈Nat.primesBelow P) : 1/(p:ℝ)≤Real.exp 1*q σ p := by
    have hPrime := Nat.prime_of_mem_primesBelow hp
    have hpR : 0<(p:ℝ) := by exact_mod_cast hPrime.pos
    have hpP : (p:ℝ)≤P := by exact_mod_cast (Nat.mem_primesBelow.mp hp).1.le
    have hS : (p:ℝ)^σ≤Real.exp 1 := by
      rw [Real.rpow_def_of_pos hpR]
      apply Real.exp_le_exp.mpr
      have H := mul_le_mul_of_nonneg_right (Real.log_le_log hpR hpP) hσ.le
      have H' : Real.log P*σ=1 := by dsimp only [σ]; field_simp [hlog.ne']
      exact H.trans_eq H'
    have hEq : 1/(p:ℝ)=(p:ℝ)^σ*q σ p := by
      rw [q,←Real.rpow_add hpR,show σ+(-1-σ)=(-1:ℝ) by ring,
        Real.rpow_neg_one,one_div]
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hS (q_bounds σ hσ hPrime).1
  calc
    _ ≤ ∑ p∈Nat.primesBelow P,Real.exp 1*q σ p := Finset.sum_le_sum hAtom
    _ = Real.exp 1*(∑ p∈Nat.primesBelow P,q σ p) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      have H := log_reference σ hσ P
      simpa only [σ,one_div,inv_inv] using H

end ActualTZPrimeReciprocalPrefix318
