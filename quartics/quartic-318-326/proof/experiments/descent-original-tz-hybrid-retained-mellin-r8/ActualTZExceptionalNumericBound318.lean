module
public import ActualSmallCoefficientPrimeBudget318
public import ActualTZFiniteIntegerTail318
public section
noncomputable section
namespace ActualTZExceptionalNumericBound318
open scoped BigOperators
open ActualTZFiniteIntegerTail318 ActualSmallCoefficientPrimeBudget318

theorem inverse_square (y : ℕ) (hy : 0<y) (S : Finset ℕ) (hS : ∀ p∈S,y<p) :
    (∑ p∈S,(1/(p:ℝ))^2)≤1/(y:ℝ) := by
  have h1 (p : ℕ) (hp : p∈S) : (1/(p:ℝ))^2=(p:ℝ)^((-1:ℝ)-1) := by
    have hp' : (0:ℝ)≤p := by positivity
    rw [show (-1:ℝ)-1= -(2:ℝ) by norm_num,Real.rpow_neg hp',Real.rpow_two,one_div,inv_pow]
  calc
    _ = ∑ p∈S,(p:ℝ)^((-1:ℝ)-1) := Finset.sum_congr rfl h1
    _ ≤ (y:ℝ)^(-(1:ℝ))/1 := tail 1 zero_lt_one y hy S hS
    _ = _ := by rw [Real.rpow_neg_one,div_one,one_div]

/-- Use the genuine marker product K after its wheel-specific size
bound, rather than discounting all collision primes by log p. -/
theorem exceptional (y K : ℕ) (hy : 1<y) (hK : 0<K) (S : Finset ℕ)
    (hS : ∀ p∈S,p.Prime ∧ y<p ∧ p∣K)
    (A : ℝ) (hSize : Real.log K≤A*(y:ℝ)) :
    (∑ p∈S,1/(p:ℝ))≤A/Real.log y := by
  have hc : (K:ℤ)≠0 := by exact_mod_cast hK.ne'
  have hData (p : ℕ) (hp : p∈S) : p.Prime ∧ y≤p ∧ (p:ℤ)∣(K:ℤ) :=
    ⟨(hS p hp).1,(hS p hp).2.1.le,by exact_mod_cast (hS p hp).2.2⟩
  have H := bad_reciprocal_le S hy hc hData
  have hyR : (1:ℝ)<y := by exact_mod_cast hy
  have hy0 : 0<(y:ℝ) := zero_lt_one.trans hyR
  have hl : 0<Real.log y := Real.log_pos hyR
  simp only [Int.natAbs_ofNat] at H
  calc
    _ ≤ Real.log K/((y:ℝ)*Real.log y) := H
    _ ≤ (A*(y:ℝ))/((y:ℝ)*Real.log y) :=
      div_le_div_of_nonneg_right hSize (mul_nonneg hy0.le hl.le)
    _ = _ := by field_simp [hy0.ne',hl.ne'] <;> ring

end ActualTZExceptionalNumericBound318
