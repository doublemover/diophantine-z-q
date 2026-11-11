module
public import ActualOrdinaryEulerHarmonic318
public section
noncomputable section
namespace ActualFiniteEulerExclusions318
open scoped BigOperators
open FixedSieveExceptionalPrimes318 ActualSieveMultiplicativeDensity318 ActualSieveEulerProduct318
set_option maxHeartbeats 18000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- EXACT finite exceptional set for the original local density:
original coefficient exceptions and the original large-prime cutoff. -/
@[expose] def excludedSet (κ : ℤ) (γ : J → ℤ) : Finset ℕ :=
  (exceptionalPrimes κ γ ∪ Finset.range (16*(Fintype.card J+2))).filter Nat.Prime
lemma excluded_prime (κ : ℤ) (γ : J → ℤ) (p : ℕ) (hp : p∈excludedSet κ γ) : p.Prime :=
  (Finset.mem_filter.mp hp).2
lemma actual_selected_eq_difference (κ : ℤ) (γ : J → ℤ) (N : ℕ) :
    selected κ γ N=Nat.primesBelow N \ excludedSet κ γ := by
  classical
  ext p
  simp only [selected,excludedSet,Finset.mem_filter,Finset.mem_range,Finset.mem_union,
    Finset.mem_sdiff,Nat.mem_primesBelow,Eligible]
  omega

/-- Uniform finite-subproduct bound with NO sign assumption beyond
positivity of the actual factors. Some character factors are below1;
they are not incorrectly discarded using monotonicity of products. -/
lemma finite_subproduct_bound (f : ℕ → ℝ) (F : Finset ℕ) (hf : ∀p∈F,0<f p) :
    ∃ U : ℝ,0<U ∧ ∀ A : Finset ℕ,A⊆F → (∏p∈A,f p)≤U := by
  let B : ℝ := ∑A∈F.powerset,∏p∈A,f p
  have hterm (A : Finset ℕ) (hA : A∈F.powerset) : 0≤∏p∈A,f p :=
    Finset.prod_nonneg (fun p hp => (hf p ((Finset.mem_powerset.mp hA) hp)).le)
  have hB : 0≤B := Finset.sum_nonneg hterm
  refine ⟨1+B,by linarith,?_⟩
  intro A hA
  have hh : (∏p∈A,f p)≤B := Finset.single_le_sum hterm (Finset.mem_powerset.mpr hA)
  linarith

/-- Actual removal at the CONSUMER: the full prime product is bounded
by one fixed positive constant times the product on the exact original
selected primes, uniformly over all cutoffs. -/
theorem actual_selected_product_comparison (κ : ℤ) (γ : J → ℤ) (f : ℕ → ℝ)
    (hf : ∀p,p.Prime → 0<f p) :
    ∃ U : ℝ,0<U ∧ ∀ N,
      (∏p∈Nat.primesBelow N,f p)≤U*(∏p∈selected κ γ N,f p) := by
  obtain ⟨U,hU,hbound⟩ := finite_subproduct_bound f (excludedSet κ γ)
    (fun p hp => hf p (excluded_prime κ γ p hp))
  refine ⟨U,hU,?_⟩
  intro N
  have hsel : selected κ γ N⊆Nat.primesBelow N := by
    rw [actual_selected_eq_difference]
    exact Finset.sdiff_subset
  have hrem : Nat.primesBelow N \ selected κ γ N⊆excludedSet κ γ := by
    intro p hp
    have hh := Finset.mem_sdiff.mp hp
    by_contra h
    apply hh.2
    rw [actual_selected_eq_difference]
    exact Finset.mem_sdiff.mpr ⟨hh.1,h⟩
  have hprod : 0≤∏p∈selected κ γ N,f p :=
    Finset.prod_nonneg (fun p hp => (hf p (selected_prime κ γ N p hp)).le)
  have hh := mul_le_mul_of_nonneg_right (hbound _ hrem) hprod
  rw [Finset.prod_sdiff hsel] at hh
  exact hh

end ActualFiniteEulerExclusions318
