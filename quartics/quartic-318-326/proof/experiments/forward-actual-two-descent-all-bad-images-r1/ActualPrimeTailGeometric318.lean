module
public import ActualPrimeDyadicPower318
public section
noncomputable section
namespace ActualPrimeTailGeometric318
open scoped BigOperators
open ActualPrimeDyadicCount318 ActualPrimeDyadicPower318
set_option maxHeartbeats 18000000

lemma geometric_partial_bound (r : ℝ) (hr0 : 0≤r) (hr1 : r<1) (K : ℕ) :
    (∑k∈Finset.range K,r^k)≤1/(1-r) := by
  have he : (∑k∈Finset.range K,r^k)*(1-r)=1-r^K := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ,add_mul,ih,pow_succ]
      ring
  apply (le_div_iff₀ (by linarith : 0<1-r)).mpr
  rw [he]
  linarith [pow_nonneg hr0 K]

lemma actual_dyadic_union_bound (N : ℕ) (hN : 1<N) (δ : ℝ) (hδ : 0<δ) (K : ℕ) :
    (∑p∈Finset.Ico N (lower N K),primeWeight δ p)≤
      ∑k∈Finset.range K,amplitude N δ*ratio δ^k := by
  induction K with
  | zero => simp [lower]
  | succ K ih =>
    rw [←Finset.sum_Ico_consecutive (lower_base_le N K) (lower_mono N (Nat.le_succ K)),
      Finset.sum_range_succ]
    exact add_le_add ih (actual_block_power N hN δ hδ K)

lemma self_lt_two_pow (K : ℕ) : K<2^K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [pow_succ]
    have hp : 0<(2:ℕ)^K := pow_pos (by norm_num) _
    omega

/-- Uniform bound for EVERY actual finite prime set above N. The tail
is controlled by Chebyshev prime blocks, not the larger integer tail
whose logarithmic loss would break the moving-boundary argument. -/
theorem actual_finite_prime_tail (N : ℕ) (hN : 1<N) (δ : ℝ) (hδ : 0<δ)
    (S : Finset ℕ) (hS : ∀p∈S,p.Prime ∧ N≤p) :
    (∑p∈S,(p:ℝ)^(-(1+δ)))≤amplitude N δ/(1-ratio δ) := by
  let K := S.sup id+1
  have hsub : S⊆Finset.Ico N (lower N K) := by
    intro p hp
    have hsup : p≤S.sup id := Finset.le_sup (f := id) hp
    have hpK : p<K := by dsimp [K];omega
    have ht := self_lt_two_pow K
    have hN1 : 1≤N := by omega
    have hpow : 2^K≤lower N K := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2^K) hN1
    exact Finset.mem_Ico.mpr ⟨(hS p hp).2,(hpK.trans ht).trans_le hpow⟩
  have h0 := (ratio_bounds δ hδ).1
  have h1 := (ratio_bounds δ hδ).2
  calc
    _ = ∑p∈S,primeWeight δ p := Finset.sum_congr rfl
      (fun p hp => by rw [primeWeight,if_pos (hS p hp).1])
    _ ≤ ∑p∈Finset.Ico N (lower N K),primeWeight δ p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => primeWeight_nonneg δ p)
    _ ≤ ∑k∈Finset.range K,amplitude N δ*ratio δ^k := actual_dyadic_union_bound N hN δ hδ K
    _ = amplitude N δ*∑k∈Finset.range K,ratio δ^k := (Finset.mul_sum _ _ _).symm
    _ ≤ amplitude N δ*(1/(1-ratio δ)) := mul_le_mul_of_nonneg_left
      (geometric_partial_bound _ h0 h1 K) (amplitude_nonneg N hN δ)
    _ = _ := by ring

end ActualPrimeTailGeometric318
