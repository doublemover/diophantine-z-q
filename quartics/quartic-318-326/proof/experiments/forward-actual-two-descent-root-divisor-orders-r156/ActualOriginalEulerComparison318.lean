module
public import ActualCorrectionUniformBounds318
public section
noncomputable section
namespace ActualOriginalEulerComparison318
open scoped BigOperators
open ActualSieveEulerProduct318 ActualSieveMultiplicativeDensity318 ActualRemovedEulerFactor318
open ActualModFourSieveCharacter318 ActualCorrectionUniformBounds318
set_option maxHeartbeats 20000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def ordinaryEuler (κ : ℤ) (γ : J → ℤ) (N : ℕ) : ℝ :=
  ∏ p∈selected κ γ N,(1-1/(p:ℝ))⁻¹
@[expose] def characterEuler (κ : ℤ) (γ : J → ℤ) (N : ℕ) : ℝ :=
  ∏ p∈selected κ γ N,(1-realCharacter p/(p:ℝ))⁻¹

lemma selected_correction_eq_partial (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N : ℕ) :
    (∏ p∈selected κ γ N,factor κ γ j₀ p)=partialCorrection κ γ j₀ N := by
  classical
  rw [selected,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : Eligible κ γ p
  · rw [if_pos hp]
  · simp only [if_neg hp,factor,dif_neg hp]

/-- Exact decomposition at the original retained prime. The actual
finite-field character is identified with the genuine mod-four
Dirichlet character before forming the consumer product. -/
lemma original_local_inverse (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ : J) (p : ℕ) (hp : Eligible κ γ p) :
    (1-nu κ γ j₀ p)⁻¹=(factor κ γ j₀ p)⁻¹*
      ((1-1/(p:ℝ))⁻¹)^(Fintype.card J)*((1-realCharacter p/(p:ℝ))⁻¹)^2 := by
  letI : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨hp2,_,_⟩ := FixedSieveExceptionalPrimes318.outside_conditions κ hκ γ hγ p hp.1 hp.2.1
  have hd := factor_decomposition κ γ j₀ p hp
  have hn : nu κ γ j₀ p=
      (FiniteSieveDensity318.density (κ:ZMod p) (fun j => (γ j:ZMod p)) j₀:ℝ) := by
    rw [nu_at_prime κ γ j₀ p hp.1]
    rfl
  rw [←hn,original_prime_character p hp2] at hd
  rw [hd,EulerBinomialError318.model]
  simp only [mul_inv,inv_pow,mul_one_div]
  ring

/-- The FULL original Euler denominator is decomposed exactly. The
correction, ordinary factor and CHARACTER factor all use the same
original selected set and coefficient count. -/
theorem actual_full_euler_identity (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ : J) (N : ℕ) :
    fullEuler κ γ j₀ N=(partialCorrection κ γ j₀ N)⁻¹*
      ordinaryEuler κ γ N^(Fintype.card J)*characterEuler κ γ N^2 := by
  calc
    _ = ∏ p∈selected κ γ N,(factor κ γ j₀ p)⁻¹*
        ((1-1/(p:ℝ))⁻¹)^(Fintype.card J)*((1-realCharacter p/(p:ℝ))⁻¹)^2 := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [one_div] using original_local_inverse κ hκ γ hγ j₀ p
        (selected_eligible κ γ N p hp)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,
        Finset.prod_inv_distrib,selected_correction_eq_partial,
        Finset.prod_pow,Finset.prod_pow]
      rfl

lemma ordinary_euler_pos (κ : ℤ) (γ : J → ℤ) (N : ℕ) : 0<ordinaryEuler κ γ N := by
  apply Finset.prod_pos
  intro p hp
  have hP : (1:ℝ)<p := by exact_mod_cast (selected_prime κ γ N p hp).one_lt
  have hinv : 1/(p:ℝ)<1 := by
    apply (div_lt_iff₀ (by linarith : (0:ℝ)<p)).mpr
    simpa only [one_mul] using hP
  exact inv_pos.mpr (by linarith)
lemma character_euler_pos (κ : ℤ) (γ : J → ℤ) (N : ℕ) : 0<characterEuler κ γ N := by
  apply Finset.prod_pos
  intro p hp
  have hP : (1:ℝ)<p := by exact_mod_cast (selected_prime κ γ N p hp).one_lt
  have hh : realCharacter p/(p:ℝ)<1 := by
    apply (div_lt_iff₀ (by linarith : (0:ℝ)<p)).mpr
    simpa only [one_mul] using (real_character_le_one p).trans_lt hP
  exact inv_pos.mpr (by linarith)

/-- A genuine uniform comparison to the ordinary and actual character
Euler products. Their remaining logarithmic growth/boundary-truncation
estimates are not asserted here. -/
theorem actual_uniform_euler_comparison (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ U : ℝ,0<U ∧ ∀ N,
      ordinaryEuler κ γ N^(Fintype.card J)*characterEuler κ γ N^2/U≤fullEuler κ γ j₀ N := by
  obtain ⟨U,hU,hbound⟩ := actual_uniform_upper κ hκ γ hγ j₀ j₁ h0 h1
  refine ⟨U,hU,?_⟩
  intro N
  rw [actual_full_euler_identity κ hκ γ hγ j₀ N]
  have hp := partial_positive κ hκ γ hγ j₀ j₁ h0 h1 N
  have hi := one_div_le_one_div_of_le hp (hbound N)
  have hn : 0≤ordinaryEuler κ γ N^(Fintype.card J)*characterEuler κ γ N^2 := by
    have ho := ordinary_euler_pos κ γ N
    positivity
  have hh := mul_le_mul_of_nonneg_left hi hn
  convert hh using 1 <;> ring

end ActualOriginalEulerComparison318
