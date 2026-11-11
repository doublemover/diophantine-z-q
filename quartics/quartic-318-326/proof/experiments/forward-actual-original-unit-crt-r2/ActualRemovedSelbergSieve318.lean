module
public import FiniteSelbergMinimizer318
public section
noncomputable section
namespace ActualRemovedSelbergSieve318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
open ActualSelbergDivisorChoices318 ActualSelbergDivisorWeights318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Actual prime-removal sieve, retaining every original source point,
fiber weight, total mass and local density. Only the prime product changes. -/
@[expose] def sieve (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) : BoundingSieve := by
  classical
  exact { OriginalWeightedSelberg318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N S with
    prodPrimes := product κ γ N excluded
    prodPrimes_squarefree := ActualSelbergDivisorChoices318.product_squarefree κ γ N excluded
    nu_pos_of_prime := fun p hp hd =>
      (retained_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 N excluded
        ⟨p,(ActualSelbergDivisorChoices318.prime_dvd_product_iff κ γ N excluded p hp).mp hd⟩).1
    nu_lt_one_of_prime := fun p hp hd =>
      ((retained_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 N excluded
        ⟨p,(ActualSelbergDivisorChoices318.prime_dvd_product_iff κ γ N excluded p hp).mp hd⟩).2).trans_lt
        (by norm_num) }

lemma actual_sifted_sum (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).siftedSum=
      ∑ v∈S,if Nat.Coprime (product κ γ N excluded) (OriginalWeightedSelberg318.key κ γ v)
        then OriginalWeightedSelberg318.weight κ γ v else 0 := by
  classical
  exact OriginalWeightedSelberg318.fiber_sum κ γ S (Nat.Coprime (product κ γ N excluded))

lemma modulus_dvd_modulus (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (a b : PrimeIndex κ γ N excluded → Bool) :
    modulus κ γ N excluded a∣modulus κ γ N excluded b ↔
      ∀ i,a i=true → b i=true := by
  constructor
  · intro hd i ha
    exact (prime_dvd_modulus κ γ N excluded b i).mp
      (((prime_dvd_modulus κ γ N excluded a i).mpr ha).trans hd)
  · intro hh
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    cases ha : a i
    · simp only [ha,Bool.false_eq_true,if_false,one_dvd]
    · simp only [ha,hh i ha,if_true,dvd_refl]

lemma zeta_is_divisibility (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (a b : PrimeIndex κ γ N excluded → Bool) :
    FiniteBooleanMobius318.zeta a b=
      if modulus κ γ N excluded a∣modulus κ γ N excluded b then 1 else 0 := by
  classical
  rw [FiniteBooleanMobius318.zeta_indicator,modulus_dvd_modulus]

lemma actual_cut_downward (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) (z : ℝ)
    (a b : PrimeIndex κ γ N excluded → Bool)
    (hab : ∀ i,a i=true → b i=true) (hb : (modulus κ γ N excluded b:ℝ)<z) :
    (modulus κ γ N excluded a:ℝ)<z := by
  have hd := (modulus_dvd_modulus κ γ N excluded a b).mpr hab
  have hle := Nat.le_of_dvd (modulus_pos κ γ N excluded b) hd
  exact (by exact_mod_cast hle : (modulus κ γ N excluded a:ℝ)≤modulus κ γ N excluded b).trans_lt hb

lemma actual_modulus_nu_pos (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (a : PrimeIndex κ γ N excluded → Bool) : 0<nu κ γ j₀ (modulus κ γ N excluded a) := by
  let s := sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded ∅
  exact @BoundingSieve.nu_pos_of_dvd_prodPrimes s _ (modulus_dvd κ γ N excluded a)
lemma actual_modulus_terms_pos (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (a : PrimeIndex κ γ N excluded → Bool) : 0<terms κ γ j₀ (modulus κ γ N excluded a) := by
  let s := sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded ∅
  exact @BoundingSieve.selbergTerms_pos s _ (modulus_dvd κ γ N excluded a)

end ActualRemovedSelbergSieve318
