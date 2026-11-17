module
public import ActualRemovedSelbergSieve318
public section
noncomputable section
namespace ActualSelbergCoefficients318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
open ActualSelbergDivisorChoices318 ActualSelbergDivisorWeights318 ActualRemovedSelbergSieve318
set_option maxHeartbeats 20000000
variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def choiceNu (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ)
    (a : PrimeIndex κ γ N excluded → Bool) : ℝ := nu κ γ j₀ (modulus κ γ N excluded a)
@[expose] def choiceTerm (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ)
    (a : PrimeIndex κ γ N excluded → Bool) : ℝ := terms κ γ j₀ (modulus κ γ N excluded a)
@[expose] def choiceCut (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) (z : ℝ)
    (a : PrimeIndex κ γ N excluded → Bool) : Prop := (modulus κ γ N excluded a:ℝ)<z
@[expose] def bits (κ : ℤ) (γ : J → ℤ) (N excluded d : ℕ)
    (i : PrimeIndex κ γ N excluded) : Bool := decide (i.1∣d)

/-- Explicit finite Mobius-inverse coefficients on actual natural
moduli. Nondivisors are assigned zero, not silently identified with
their retained-prime support. -/
@[expose] def coefficients (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ) (z : ℝ)
    (d : ℕ) : ℝ := by
  classical
  exact if d∣product κ γ N excluded then
    FiniteSelbergMinimizer318.coefficient (choiceNu κ γ j₀ N excluded)
      (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z) (bits κ γ N excluded d)
    else 0

lemma bits_modulus (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (a : PrimeIndex κ γ N excluded → Bool) : bits κ γ N excluded (modulus κ γ N excluded a)=a := by
  funext i
  have hh := prime_dvd_modulus κ γ N excluded a i
  cases ha : a i <;> simp_all [bits]
lemma coefficient_at_modulus (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ) (z : ℝ)
    (a : PrimeIndex κ γ N excluded → Bool) :
    coefficients κ γ j₀ N excluded z (modulus κ γ N excluded a)=
      FiniteSelbergMinimizer318.coefficient (choiceNu κ γ j₀ N excluded)
        (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z) a := by
  classical
  simp only [coefficients,if_pos (modulus_dvd κ γ N excluded a),bits_modulus]

lemma actual_mass_identity (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) (z : ℝ) :
    FiniteSelbergMinimizer318.mass (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z)=
      denominator κ γ j₀ N excluded z := by
  classical
  rw [actual_denominator_eq_truncated κ hκ γ hγ j₀ j₁ h0 h1]
  unfold FiniteSelbergMinimizer318.mass truncated choiceCut choiceTerm
  apply Finset.sum_congr rfl
  intro a _
  rw [actual_modulus_weight κ hκ γ hγ j₀ j₁ h0 h1]

lemma actual_mass_pos (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) (z : ℝ) (hz : 1<z) :
    0<FiniteSelbergMinimizer318.mass (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z) := by
  classical
  apply FiniteSelbergMinimizer318.mass_pos
  · exact actual_modulus_terms_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded
  · simpa [choiceCut,modulus] using hz

lemma actual_coefficient_one (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) (z : ℝ) (hz : 1<z) :
    coefficients κ γ j₀ N excluded z 1=1 := by
  classical
  have he : modulus κ γ N excluded (fun _ => false)=1 := by simp [modulus]
  rw [←he,coefficient_at_modulus]
  apply FiniteSelbergMinimizer318.coefficient_empty
  · simpa only [choiceNu,he] using (nu_multiplicative κ γ j₀).map_one
  · exact (actual_mass_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz).ne'

/-- Actual natural-number support below the SAME strict level. -/
lemma actual_coefficient_support (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ)
    (z : ℝ) (d : ℕ) (hd : z≤(d:ℝ)) : coefficients κ γ j₀ N excluded z d=0 := by
  classical
  unfold coefficients
  split_ifs with hdiv
  · apply FiniteSelbergMinimizer318.coefficient_support
    · exact actual_cut_downward κ γ N excluded z
    · unfold choiceCut bits
      rw [actual_divisor_reconstruction κ γ N excluded d hdiv]
      exact not_lt_of_ge hd
  · rfl

/-- Actual diagonal coordinate, after moving the entire original
integer-divisor sum through the exact divisor equivalence. -/
lemma actual_diagonal_coordinate (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) (z : ℝ)
    (a : PrimeIndex κ γ N excluded → Bool) :
    (∑ d∈(product κ γ N excluded).divisors,
      if modulus κ γ N excluded a∣d then nu κ γ j₀ d*coefficients κ γ j₀ N excluded z d else 0)=
      FiniteSelbergMinimizer318.target (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z) a := by
  classical
  have he := Equiv.sum_comp (divisorEquiv κ γ N excluded)
    (fun d : ↥(product κ γ N excluded).divisors =>
      if modulus κ γ N excluded a∣d.1 then nu κ γ j₀ d.1*coefficients κ γ j₀ N excluded z d.1 else 0)
  rw [Finset.sum_coe_sort] at he
  rw [←he]
  have hs := FiniteSelbergMinimizer318.diagonal_coordinates
    (choiceNu κ γ j₀ N excluded) (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z)
    (fun b => (actual_modulus_nu_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded b).ne') a
  convert hs using 1
  apply Finset.sum_congr rfl
  intro b _
  change (if modulus κ γ N excluded a∣modulus κ γ N excluded b then
    nu κ γ j₀ (modulus κ γ N excluded b)*coefficients κ γ j₀ N excluded z (modulus κ γ N excluded b)
    else 0)=_
  rw [coefficient_at_modulus,zeta_is_divisibility]
  split_ifs <;> simp only [one_mul,zero_mul,choiceNu]

end ActualSelbergCoefficients318
