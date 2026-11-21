module
public import ActualTZPhysicalEulerSplit318
import all ActualTZPhysicalEulerSplit318
public section
noncomputable section
namespace ActualTZPhysicalCorrectionBound318
open scoped BigOperators
open ActualTZPhysicalEulerSplit318 ActualTZFiniteProductNearOne318
open ActualTZRegulatedPhysicalBounds318 ActualTZRegulatedPhysicalPrime318
open ActualTZRegulatedZetaAlgebra318 ActualTZMultiLinearCRT318
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def hit (W p : ℕ) (a : I→ℤ) (b : I→ℕ) : Prop :=
  ∃ i j,i≠j ∧ (p:ℤ)∣physicalConst W a b i-physicalConst W a b j

@[expose] def goodConst (k : ℕ) : ℝ := (6:ℝ)^k*errorConst k
@[expose] def badConst (k : ℕ) : ℝ :=
  (6:ℝ)^k*(((2:ℝ)^k)^2+3*(k:ℝ)+errorConst k)

theorem good_nonnegative (k : ℕ) : 0≤goodConst k :=
  mul_nonneg (by positivity) (errorConst_nonneg k)
theorem bad_nonnegative (k : ℕ) : 0≤badConst k := by
  unfold badConst
  have h := errorConst_nonneg k
  positivity

/-- Good primes give the same O_k(p⁻²); true collisions carry the
same signed difference and its O_k(p⁻¹) loss. Constants are
independent of the older neighborhoods and of σ>0. -/
theorem atom_error (W p : ℕ) (hp : p.Prime) (hc : W.Coprime p)
    (a : I→ℤ) (b : I→ℕ) (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ)
    (s t : I→ℂ) (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re) :
    ‖actualAtom W p a b s t/refAtom p s t-1‖≤
      goodConst (Fintype.card I)*(1/(p:ℝ))^2+
      badConst (Fintype.card I)*(if hit W p a b then 1/(p:ℝ) else 0) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [actualAtom,dif_pos hp,ref_is_baseline]
  by_cases h : hit W p a b
  · rw [if_pos h]
    have hRp : (p:ℝ)^(-σ)≤1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hp.one_lt.le) (neg_nonpos.mpr hσ.le)
    have hPos : 0≤(1:ℝ)/(p:ℝ) := by positivity
    have HD : ((2:ℝ)^Fintype.card I)^2*(p:ℝ)^(-σ)≤((2:ℝ)^Fintype.card I)^2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hRp (by positivity : 0≤((2:ℝ)^Fintype.card I)^2)
    have HF : (6:ℝ)^Fintype.card I*
        (((2:ℝ)^Fintype.card I)^2*(p:ℝ)^(-σ)+3*(Fintype.card I:ℝ)+errorConst (Fintype.card I))≤
        badConst (Fintype.card I) := by
      unfold badConst
      exact mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add_right HD _) _)
        (by positivity)
    have H := relative_regulated_linear W p hp a b hU σ hσ s t hs ht
    rw [←mul_assoc] at H
    exact H.trans ((mul_le_mul_of_nonneg_right HF hPos).trans
      (le_add_of_nonneg_left (mul_nonneg (good_nonnegative _) (sq_nonneg _))))
  · rw [if_neg h,mul_zero,add_zero]
    have hD : Function.Injective (primeRoot W p a b) := by
      by_contra hn
      exact h ((collision_witness W p a b hc).1 hn)
    simpa only [goodConst,mul_assoc] using relative_regulated_distinct W p hp a b σ hσ s t hs ht hc hD

/-- Exact pointwise finite ledger before taking any outer row
average; the same primality, coprimality, and shared collision
weights are used in both the analytic and native formulas. -/
theorem corrected_error (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ)
    (s t : I→ℂ) (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re) :
    ‖corrected W P a b s t-1‖ ≤
      Real.exp (goodConst (Fintype.card I)*(∑ p∈offWheel W P,(1/(p:ℝ))^2)+
        badConst (Fintype.card I)*(∑ p∈offWheel W P,if hit W p a b then 1/(p:ℝ) else 0))-1 := by
  have H := product_near_one (offWheel W P)
    (fun p => actualAtom W p a b s t/refAtom p s t)
    (fun p => goodConst (Fintype.card I)*(1/(p:ℝ))^2+
      badConst (Fintype.card I)*(if hit W p a b then 1/(p:ℝ) else 0))
    (fun p hp => atom_error W p (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1)
      (Finset.mem_filter.mp hp).2 a b hU σ hσ s t hs ht)
  simpa only [corrected,Finset.sum_add_distrib,←Finset.mul_sum] using H

end ActualTZPhysicalCorrectionBound318
