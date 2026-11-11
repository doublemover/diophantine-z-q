module
public import ActualChebyshevLogMoment318
public section
noncomputable section
namespace ActualSievePrimeMoment318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSieveEulerProduct318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def retained (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) : Finset ℕ :=
  (selected κ γ N).erase excluded
@[expose] def momentConstant (J : Type*) [Fintype J] : ℝ := 5*(Fintype.card J:ℝ)+6
lemma momentConstant_pos : 0<momentConstant J := by dsimp [momentConstant];positivity

lemma error_to_upper (g k e x : ℝ) (hk : 0≤k) (hx : 0≤x) (hx1 : x≤1) (he : e≤1)
    (herr : |g-(k+2*e)*x|≤4*(k+1)*x^2) : g≤(5*k+6)*x := by
  have hu := (abs_le.mp herr).2
  have hx2 : x^2≤x := by nlinarith
  have hr := mul_le_mul_of_nonneg_left hx2 (by positivity : 0≤4*(k+1))
  have hc := mul_le_mul_of_nonneg_right (show k+2*e≤k+2 by linarith) hx
  nlinarith only [hu,hr,hc]

/-- An explicit reciprocal-prime bound and uniform half bound for the
ACTUAL original local density, derived from its checked finite-field formula. -/
theorem actual_local_upper (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (p : ℕ) (hp : Eligible κ γ p) :
    nu κ γ j₀ p≤momentConstant J/(p:ℝ) ∧ nu κ γ j₀ p≤1/2 := by
  letI : Fact p.Prime := ⟨hp.1⟩
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.1.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.1.one_le
  have hk : (0:ℝ)≤(Fintype.card J:ℝ) := Nat.cast_nonneg _
  have he : (quadraticChar (ZMod p) (-1:ZMod p):ℝ)≤1 := by
    have hh : (quadraticChar (ZMod p) (-1:ZMod p):ℝ)=1 ∨
        (quadraticChar (ZMod p) (-1:ZMod p):ℝ)= -1 := by
      exact_mod_cast quadraticChar_dichotomy
        (show (-1:ZMod p)≠0 from neg_ne_zero.mpr one_ne_zero)
    rcases hh with hh|hh <;> rw [hh] <;> norm_num
  have herr := actual_real_error κ hκ γ hγ j₀ j₁ h0 h1 p hp.2.1
  have hdens : nu κ γ j₀ p=
      (FiniteSieveDensity318.density (κ:ZMod p) (fun j => (γ j:ZMod p)) j₀:ℝ) := by
    rw [nu_at_prime κ γ j₀ p hp.1]
    rfl
  rw [←hdens] at herr
  have hu := error_to_upper (nu κ γ j₀ p) (Fintype.card J:ℝ) _ (1/(p:ℝ)) hk
    (by positivity) (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp1) he herr
  have hu' : nu κ γ j₀ p≤momentConstant J/(p:ℝ) := by
    simpa only [momentConstant,mul_one_div] using hu
  have hlarge : 16*((Fintype.card J:ℝ)+2)≤(p:ℝ) := by exact_mod_cast hp.2.2
  have hhalf : momentConstant J/(p:ℝ)≤1/2 := by
    apply (div_le_iff₀ hpR).mpr
    dsimp [momentConstant]
    nlinarith only [hlarge,hk]
  exact ⟨hu',hu'.trans hhalf⟩

lemma retained_facts (κ : ℤ) (γ : J → ℤ) (N excluded p : ℕ)
    (hp : p∈retained κ γ N excluded) : Eligible κ γ p ∧ p<N ∧ p≠excluded := by
  have hh := Finset.mem_erase.mp hp
  have hs := Finset.mem_filter.mp hh.2
  exact ⟨hs.2,Finset.mem_range.mp hs.1,hh.1⟩

@[expose] def moment (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ) : ℝ :=
  ∑ p∈retained κ γ N excluded,nu κ γ j₀ p*Real.log (p:ℝ)
@[expose] def momentBound (J : Type*) [Fintype J] (N : ℕ) : ℝ :=
  momentConstant J*Real.log 4*(1+Real.log (N:ℝ))

/-- Genuine uniform logarithmic first moment on the original cutoff
primes after removing ANY one prime. Chebyshev's pinned theorem supplies
the elementary prime input; no Mertens or distribution estimate is assumed. -/
theorem actual_moment_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ) (hN : 1≤N) (excluded : ℕ) :
    moment κ γ j₀ N excluded≤momentBound J N := by
  have hp (p : ℕ) (hp : p∈retained κ γ N excluded) :
      nu κ γ j₀ p*Real.log (p:ℝ)≤momentConstant J*(Real.log (p:ℝ)/(p:ℝ)) := by
    have hf := retained_facts κ γ N excluded p hp
    have hh := mul_le_mul_of_nonneg_right
      (actual_local_upper κ hκ γ hγ j₀ j₁ h0 h1 p hf.1).1
      (Real.log_natCast_nonneg p)
    convert hh using 1 <;> ring
  have hs := Finset.sum_le_sum (fun p hp' => hp p hp')
  rw [←Finset.mul_sum] at hs
  have hc := ActualChebyshevLogMoment318.actual_prime_log_moment
    (retained κ γ N excluded) N hN (fun p hp' => by
      have hh := retained_facts κ γ N excluded p hp'
      exact ⟨hh.1.1,hh.2.1.le⟩)
  have ht := mul_le_mul_of_nonneg_left hc (momentConstant_pos (J := J)).le
  exact hs.trans (by simpa only [momentBound,mul_assoc] using ht)

/-- All Bernoulli factors on the ACTUAL original prime set are positive
and <=1/2. In particular, removing a prime costs a bounded Euler factor. -/
theorem retained_density_bounds (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (p : ↥(retained κ γ N excluded)) : 0<nu κ γ j₀ p.1 ∧ nu κ γ j₀ p.1≤1/2 := by
  have hf := retained_facts κ γ N excluded p.1 p.2
  have hsel := (Finset.mem_erase.mp p.2).2
  have hd := (prime_dvd_product_iff κ γ N p.1 hf.1.1).mpr hsel
  exact ⟨(actual_prime_bounds κ hκ γ hγ j₀ j₁ h0 h1 N p.1 hf.1.1 hd).1,
    (actual_local_upper κ hκ γ hγ j₀ j₁ h0 h1 p.1 hf.1).2⟩

end ActualSievePrimeMoment318
