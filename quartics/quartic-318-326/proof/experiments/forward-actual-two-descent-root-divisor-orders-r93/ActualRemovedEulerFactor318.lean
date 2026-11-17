module
public import ActualSelbergDivisorWeights318
public section
noncomputable section
namespace ActualRemovedEulerFactor318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def fullEuler (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N : ℕ) : ℝ :=
  ∏ p∈selected κ γ N,1/(1-nu κ γ j₀ p)
lemma euler_as_finset (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ) :
    euler κ γ j₀ N excluded=∏p∈retained κ γ N excluded,1/(1-nu κ γ j₀ p) := by
  simp only [euler,retainedDensity,PrimeIndex,Finset.prod_coe_sort]
lemma retained_euler_pos (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) :
    0<euler κ γ j₀ N excluded := by
  apply Finset.prod_pos
  intro i _
  have hh := retained_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 N excluded i
  have hd : 0<1-retainedDensity κ γ j₀ N excluded i := by dsimp [retainedDensity];linarith [hh.2]
  exact div_pos (by norm_num) hd

/-- Removal of any one named prime costs at most the factor two.
The estimate is proved at the CONSUMED Euler product, including the
case where the named prime was never eligible or below the cutoff. -/
theorem actual_removed_factor (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) : fullEuler κ γ j₀ N/2≤euler κ γ j₀ N excluded := by
  classical
  have hE := (retained_euler_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded).le
  by_cases hx : excluded∈selected κ γ N
  · have hg := (actual_local_upper κ hκ γ hγ j₀ j₁ h0 h1 excluded
      (selected_eligible κ γ N excluded hx)).2
    have hd : 0<1-nu κ γ j₀ excluded := by linarith
    have hf : 1/(1-nu κ γ j₀ excluded)≤2 := by
      apply (div_le_iff₀ hd).mpr
      linarith
    have hid : fullEuler κ γ j₀ N=
        (1/(1-nu κ γ j₀ excluded))*euler κ γ j₀ N excluded := by
      rw [euler_as_finset]
      exact (Finset.mul_prod_erase (selected κ γ N)
        (fun p => 1/(1-nu κ γ j₀ p)) hx).symm
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right hf hE
    linarith
  · have hid : fullEuler κ γ j₀ N=euler κ γ j₀ N excluded := by
      rw [euler_as_finset]
      simp only [retained,Finset.erase_eq_of_notMem hx,fullEuler]
    rw [hid]
    linarith

end ActualRemovedEulerFactor318
