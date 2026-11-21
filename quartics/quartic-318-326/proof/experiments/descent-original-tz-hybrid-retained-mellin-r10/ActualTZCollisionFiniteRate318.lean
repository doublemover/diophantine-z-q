module
public import ActualTZFiniteIntegerTail318
public import ActualTZPrimeReciprocalPrefix318
public section
noncomputable section
namespace ActualTZCollisionFiniteRate318
open scoped BigOperators
open ActualTZFiniteIntegerTail318 ActualTZPrimeReciprocalPrefix318

/-- Explicit off-exception finite sum rate: one y-decaying term
plus a fixed-y scale error. The upper horizon is exactly 2N. -/
theorem regular_bound (y N : ℕ) (hy : 0<y) (hN : 0<N) (S : Finset ℕ)
    (hS : ∀ p∈S,p.Prime ∧ y<p ∧ p≤2*N)
    (A M : ℝ) (hM : 0<M)
    (hLog : ∀ p∈S,(1+Real.log p)^A≤(p:ℝ)^((1:ℝ)/4)) :
    (∑ p∈S,((1+Real.log p)^A)/(p:ℝ)*(1/(p:ℝ)+1/M)) ≤
      (y:ℝ)^(-(3:ℝ)/4)/((3:ℝ)/4)+
      (((2*N:ℕ):ℝ)^((1:ℝ)/4)*(Real.exp 1*Real.log (1+Real.log (2*N+1:ℕ))))/M := by
  let F (p : ℕ) := (p:ℝ)^((-1:ℝ)-(3:ℝ)/4)
  let G (p : ℕ) := (p:ℝ)^((1:ℝ)/4)/(p:ℝ)
  have he (p : ℕ) (hp : p∈S) : G p*(1/(p:ℝ)+1/M)=F p+G p/M := by
    have hP : 0<(p:ℝ) := by exact_mod_cast (hS p hp).1.pos
    dsimp only [F,G]
    have hpow : (p:ℝ)^((1:ℝ)/4)/(p:ℝ)/(p:ℝ)=
        (p:ℝ)^((-1:ℝ)-(3:ℝ)/4) := by
      rw [←div_mul_eq_div_div,←pow_two,←Real.rpow_natCast,←Real.rpow_sub hP]
      norm_num
    -- Pull the integer p^-7/4 term before the 1/M comparison.
    have H : (p:ℝ)^((1:ℝ)/4)/(p:ℝ)*(1/(p:ℝ))=F p := by
      rw [mul_one_div]
      exact hpow
    rw [mul_add,H,mul_one_div]
  have hS' : S⊆Nat.primesBelow (2*N+1) := by
    intro p hp
    exact Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le (hS p hp).2.2,(hS p hp).1⟩
  have hG : (∑ p∈S,G p)≤((2*N:ℕ):ℝ)^((1:ℝ)/4)*
      (Real.exp 1*Real.log (1+Real.log (2*N+1:ℕ))) := by
    let A₀ := ((2*N:ℕ):ℝ)^((1:ℝ)/4)
    have A₀0 : 0≤A₀ := Real.rpow_nonneg (by positivity) _
    calc
      _ ≤ ∑ p∈S,A₀*(1/(p:ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have H : (p:ℝ)^((1:ℝ)/4)≤A₀ := Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast (hS p hp).2.2) (by norm_num)
        exact (div_le_div_of_nonneg_right H (by positivity)).trans_eq (by ring)
      _ = A₀*(∑ p∈S,1/(p:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg hS' (fun _ _ _=>by positivity)).trans
          (prefix (2*N+1) (by omega))) A₀0
  have hGood : (∑ p∈S,F p)≤(y:ℝ)^(-(3:ℝ)/4)/((3:ℝ)/4) :=
    tail ((3:ℝ)/4) (by norm_num) y hy S (fun p hp=>(hS p hp).2.1)
  calc
    _ ≤ ∑ p∈S,G p*(1/(p:ℝ)+1/M) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hLog p hp) (by positivity))
        (by positivity)
    _ = ∑ p∈S,(F p+G p/M) := Finset.sum_congr rfl he
    _ = (∑ p∈S,F p)+(∑ p∈S,G p)/M := by
      simp only [Finset.sum_add_distrib,Finset.sum_div]
    _ ≤ _ := add_le_add hGood (div_le_div_of_nonneg_right hG hM.le)

end ActualTZCollisionFiniteRate318
