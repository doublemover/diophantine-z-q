module
public import ActualTZCollisionFiniteRate318
public import ActualTZExceptionalNumericBound318
public import ActualTZCollisionPrimePartition318
import all ActualTZCollisionPrimePartition318
import all ActualTZPhysicalEulerSplit318
public section
noncomputable section
namespace ActualTZOrdinaryNumericDensity318
open scoped BigOperators
open ActualTZCollisionPrimePartition318 ActualTZPhysicalCorrectionBound318
open ActualTZPhysicalEulerSplit318 ActualTZWeightedPrimePrefix318
open ActualTZCollisionFiniteRate318 ActualTZExceptionalNumericBound318

@[expose] def Gbound (k : ℕ) (A : ℝ) (y : ℕ) : ℝ :=
  goodConst k/(y:ℝ)+badConst k*(A/Real.log y)

@[expose] def Fbound (N : ℕ) (M : ℝ) : ℝ :=
  (((2*N:ℕ):ℝ)^((1:ℝ)/4)*(Real.exp 1*Real.log (1+Real.log (2*N+1:ℕ))))/M

@[expose] def multiplier (k : ℕ) (C : ℝ) : ℝ :=
  Real.exp (badConst k)*(badConst k*C)

@[expose] def tailY (y : ℕ) : ℝ := (y:ℝ)^(-((3:ℝ)/4))/((3:ℝ)/4)

/-- The leading scalar is independent of the moving Euler universe. -/
@[expose] def leading (k : ℕ) (A C : ℝ) (y : ℕ) : ℝ :=
  (Real.exp (Gbound k A y)-1)+Real.exp (Gbound k A y)*multiplier k C*tailY y

private theorem off_gt (W P y : ℕ) (hWheel : ∀ p,p.Prime→p≤y→p∣W)
    (p : ℕ) (hp : p∈offWheel W P) : y<p := by
  obtain ⟨hP,hC⟩ := Finset.mem_filter.mp hp
  have hPrime := Nat.prime_of_mem_primesBelow hP
  by_contra h
  exact (hPrime.dvd_iff_not_coprime.mp (hWheel p hPrime (by omega))) hC.symm

theorem G_le (W P y K k : ℕ) (hy : 1<y) (hK : 0<K)
    (hWheel : ∀ p,p.Prime→p≤y→p∣W) (A : ℝ) (hA : Real.log K≤A*(y:ℝ)) :
    goodConst k*(∑ p∈offWheel W P,(1/(p:ℝ))^2)+badConst k*extra W P K≤Gbound k A y := by
  have hY : 0<y := by omega
  have hOne := inverse_square y hY (offWheel W P) (off_gt W P y hWheel)
  have hTwo : extra W P K≤A/Real.log y := by
    unfold extra
    apply exceptional y K hy hK _ _ A hA
    intro p hp
    obtain ⟨hP,hD⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hP).1,off_gt W P y hWheel p hP,hD⟩
  unfold Gbound
  exact add_le_add
    ((mul_le_mul_of_nonneg_left hOne (good_nonnegative k)).trans_eq (by ring))
    (mul_le_mul_of_nonneg_left hTwo (bad_nonnegative k))

theorem regular_le (k y N K : ℕ) (hy : 0<y) (hN : 0<N) (C M : ℝ) (hC : 0≤C) (hM : 0<M)
    (hLog : ∀ p : ℕ,y<p→(1+Real.log p)^(badConst k*Real.exp 1)≤(p:ℝ)^((1:ℝ)/4)) :
    (∑ p∈regular y N K,prefixWeight (badConst k) p*(C*(1/(p:ℝ)+1/M)))≤
      multiplier k C*(tailY y+Fbound N M) := by
  have hS (p : ℕ) (hp : p∈regular y N K) : p.Prime ∧ y<p ∧ p≤2*N := by
    obtain ⟨hP,hY,_⟩ := Finset.mem_filter.mp hp
    obtain ⟨hN,hPr⟩ := Nat.mem_primesBelow.mp hP
    exact ⟨hPr,hY,by omega⟩
  have hMul : 0≤multiplier k C := by
    unfold multiplier
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (bad_nonnegative k) hC)
  calc
    _ = multiplier k C*(∑ p∈regular y N K,
      (1+Real.log p)^(badConst k*Real.exp 1)/(p:ℝ)*(1/(p:ℝ)+1/M)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      unfold multiplier prefixWeight
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hMul
      simpa only [tailY,Fbound,neg_div] using
        (regular_bound y N hy hN (regular y N K) hS _ M hM (fun p hp=>hLog p (hS p hp).2.1))

/-- Native scalar assembly of the actual ordinary collision budget.
Only the supplied finite interval slot range, marker size, and
positive fine range occur. No equality to a pointwise-small claim. -/
theorem numeric_bound (W P y N K k : ℕ) (hy : 1<y) (hN : 0<N) (hK : 0<K)
    (hWheel : ∀ p,p.Prime→p≤y→p∣W)
    (A C M : ℝ) (hC : 0≤C) (hM : 0<M) (hA : Real.log K≤A*(y:ℝ))
    (hLog : ∀ p : ℕ,y<p→(1+Real.log p)^(badConst k*Real.exp 1)≤(p:ℝ)^((1:ℝ)/4)) :
    let G := goodConst k*(∑ p∈offWheel W P,(1/(p:ℝ))^2)+badConst k*extra W P K
    (Real.exp G-1)+Real.exp G*(∑ p∈regular y N K,
      prefixWeight (badConst k) p*(C*(1/(p:ℝ)+1/M)))≤
      leading k A C y+Real.exp (Gbound k A y)*multiplier k C*Fbound N M := by
  intro G
  have hE : Real.exp G≤Real.exp (Gbound k A y) :=
    Real.exp_le_exp.mpr (G_le W P y K k hy hK hWheel A hA)
  have hR := regular_le k y N K (by omega) hN C M hC hM hLog
  have hR₀ : 0≤∑ p∈regular y N K,prefixWeight (badConst k) p*(C*(1/(p:ℝ)+1/M)) := by
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (weight_nonneg _ (bad_nonnegative _) p (regular_prime y N K p hp))
      (mul_nonneg hC (by positivity))
  calc
    _ ≤ (Real.exp (Gbound k A y)-1)+
        Real.exp (Gbound k A y)*(multiplier k C*(tailY y+Fbound N M)) :=
      add_le_add (sub_le_sub_right hE _) (mul_le_mul hE hR hR₀ (Real.exp_pos _).le)
    _ = _ := by unfold leading; ring

end ActualTZOrdinaryNumericDensity318
