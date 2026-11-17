module
public import FiniteImprimitiveCorrection318
public section
noncomputable section
namespace ActualOriginalResidueRemainder318
open scoped BigOperators
open QuadricCRTAssembly318 ActualPrimitiveResidueMap318 ActualSieveMultiplicativeDensity318
open ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318 ActualSelbergDivisorChoices318
open ActualRemovedSelbergSieve318 FiniteImprimitiveCorrection318 FiniteWeightedResidueDiscrepancy318
set_option maxHeartbeats 24000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def PrimeIndex (d : ℕ) := ↥d.primeFactors
@[expose] def prime (d : ℕ) (i : PrimeIndex d) : ℕ := i.1
lemma prime_prime (d : ℕ) (i : PrimeIndex d) : (prime d i).Prime := Nat.prime_of_mem_primeFactors i.2
lemma prime_injective (d : ℕ) : Function.Injective (prime d) := fun _ _ h => Subtype.ext h
@[expose] def PrimitiveAtDivisor (κ : ℤ) (d : ℕ) := PrimitiveAt (prime d) κ

lemma actual_divisor_product (κ : ℤ) (γ : J → ℤ) (N excluded d : ℕ)
    (hd : d∣product κ γ N excluded) : (∏i : PrimeIndex d,prime d i)=d := by
  change (∏i : ↥d.primeFactors,i.1)=d
  rw [Finset.prod_coe_sort,Nat.prod_primeFactors_of_squarefree
    (Squarefree.squarefree_of_dvd hd (product_squarefree κ γ N excluded))]

/-- The ratio consumed by the actual sieve at EVERY retained divisor
is the density on the actual primitive residue space at that SAME divisor. -/
theorem original_divisor_residue_density (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ : J) (N excluded d : ℕ)
    (hd : d∣product κ γ N excluded) :
    (Nat.card {r : Residues (prime d) κ // Bad (prime d) κ γ r}:ℝ)/
      (Nat.card (Residues (prime d) κ):ℝ)=nu κ γ j₀ d := by
  have hf (i : PrimeIndex d) : ActualSieveEulerProduct318.Eligible κ γ (prime d i) := by
    have hh := (prime_dvd_product_iff κ γ N excluded (prime d i) (prime_prime d i)).mp
      ((Nat.dvd_of_mem_primeFactors i.2).trans hd)
    exact (retained_facts κ γ N excluded (prime d i) hh).1
  have hgood (i : PrimeIndex d) := FixedSieveExceptionalPrimes318.outside_conditions
    κ hκ γ hγ (prime d i) (hf i).1 (hf i).2.1
  have hh := actual_residue_density (prime d) (prime_prime d) (prime_injective d) κ
    (fun i => (hgood i).1) (fun i => (hgood i).2.1) γ j₀
  rw [←original_product_density (prime d) (prime_prime d) (prime_injective d) κ γ j₀,
    actual_divisor_product κ γ N excluded d hd] at hh
  exact hh

/-- Actual primitive source discrepancy in terms of literal weighted
residue fibers. The density and divisibility event are constructed from
the original data, not assumptions of uniform integer distribution. -/
theorem original_primitive_fiber_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ : J) (N excluded d : ℕ)
    (hd : d∣product κ γ N excluded)
    (S : Finset {v : Quadric κ // PrimitiveAtDivisor κ d v}) :
    letI := residueFintype (prime d) (prime_prime d) κ
    let A := Finset.univ.filter (Bad (prime d) κ γ)
    let w := fun v : {v : Quadric κ // PrimitiveAtDivisor κ d v} =>
      OriginalWeightedSelberg318.weight κ γ v.1
    |(∑v∈S,if d∣OriginalWeightedSelberg318.key κ γ v.1 then w v else 0)-
      nu κ γ j₀ d*(∑v∈S,w v)|≤
      ∑r∈A,|fiber S w (residueMap (prime d) κ) r-
        (∑v∈S,w v)/(Nat.card (Residues (prime d) κ):ℝ)| := by
  classical
  letI := residueFintype (prime d) (prime_prime d) κ
  let A := Finset.univ.filter (Bad (prime d) κ γ)
  let w := fun v : {v : Quadric κ // PrimitiveAtDivisor κ d v} =>
    OriginalWeightedSelberg318.weight κ γ v.1
  have hdens : (A.card:ℝ)/(Nat.card (Residues (prime d) κ):ℝ)=nu κ γ j₀ d := by
    have hh := original_divisor_residue_density κ hκ γ hγ j₀ N excluded d hd
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,A] using hh
  have he (v : {v : Quadric κ // PrimitiveAtDivisor κ d v}) :
      residueMap (prime d) κ v∈A ↔ d∣OriginalWeightedSelberg318.key κ γ v.1 := by
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←original_product_key (prime d) (prime_prime d) (prime_injective d),
      actual_divisor_product κ γ N excluded d hd]
  have hh := actual_discrepancy_bound S w (residueMap (prime d) κ) A
    ((∑v∈S,w v)/(Nat.card (Residues (prime d) κ):ℝ))
  simp_rw [he] at hh
  have hm : (A.card:ℝ)*((∑v∈S,w v)/(Nat.card (Residues (prime d) κ):ℝ))=
      nu κ γ j₀ d*(∑v∈S,w v) := by
    rw [←hdens]
    ring
  rw [hm] at hh
  exact hh

/-- The exact original multSum counts actual points with all their
weights, even when many different original points have the same key. -/
lemma original_mult_sum (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded d : ℕ)
    (S : Finset (Quadric κ)) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).multSum d=
      event S (OriginalWeightedSelberg318.weight κ γ)
        (fun v => d∣OriginalWeightedSelberg318.key κ γ v) :=
  OriginalWeightedSelberg318.fiber_sum κ γ S (fun n => d∣n)

/-- The actual remainder separates primitive and imprimitive source
points. Its additional error is bounded by the ACTUAL imprimitive
weighted mass, which cannot be silently removed by finite CRT. -/
theorem original_remainder_primitive_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded d : ℕ) (hd : d∣product κ γ N excluded) (S : Finset (Quadric κ)) :
    |(sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).rem d|≤
      |(sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded
        (S.filter (PrimitiveAtDivisor κ d))).rem d|+
      ∑v∈S.filter (fun v => ¬PrimitiveAtDivisor κ d v),OriginalWeightedSelberg318.weight κ γ v := by
  classical
  let s := sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S
  have hn : 0≤nu κ γ j₀ d := (@BoundingSieve.nu_pos_of_dvd_prodPrimes s d hd).le
  have hn1 : nu κ γ j₀ d≤1 := by
    by_cases he : d=1
    · rw [he,(nu_multiplicative κ γ j₀).map_one]
    · exact (@BoundingSieve.nu_lt_one_of_dvd_prodPrimes s d hd he).le
  have hh := actual_imprimitive_error_bound S (OriginalWeightedSelberg318.weight κ γ)
    (PrimitiveAtDivisor κ d) (fun v => d∣OriginalWeightedSelberg318.key κ γ v)
    (nu κ γ j₀ d) hn hn1 (fun v _ => OriginalWeightedSelberg318.weight_nonneg κ γ v)
  simp only [BoundingSieve.rem,original_mult_sum]
  exact hh

end ActualOriginalResidueRemainder318
