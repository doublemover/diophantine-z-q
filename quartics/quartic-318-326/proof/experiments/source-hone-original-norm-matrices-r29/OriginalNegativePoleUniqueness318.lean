module
public import OriginalInfinityCoefficient318

public section
noncomputable section
namespace OriginalNegativePoleUniqueness318
open OriginalInfinityCoefficient318 RootOrderMonomialBasis318 ContactInfinityRegularFractions318
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

@[expose] def poleTerm (q : ℚ) (k : ℕ) (i : ThreeIndex) : OverlapRing c :=
  algebraMap ℚ (OverlapRing c) q * (inverseU c)^k *
    InfinityOverlapLocalization318.toOpen c (ContactHOneOrderBases318.infinityBasis c i)

@[expose] def negativeSum (q : ℕ → ThreeIndex → ℚ) (N : ℕ) : OverlapRing c :=
  ∑ k ∈ Finset.range N, ∑ i, poleTerm c (q k i) (k+1) i

@[expose] def clearedSum (q : ℕ → ThreeIndex → ℚ) (N : ℕ) : InfinityRing c :=
  ∑ k ∈ Finset.range N, ∑ i, infinityTerm c (q k i) (N-(k+1)) i

theorem inverse_lower_mul (k N : ℕ) (hk : k ≤ N) :
    (inverseU c)^k * (SourceInfinityOverlap318.u c)^N = (SourceInfinityOverlap318.u c)^(N-k) := by
  have he : N = k + (N-k) := by omega
  calc
    _ = (inverseU c)^k * ((SourceInfinityOverlap318.u c)^k *
      (SourceInfinityOverlap318.u c)^(N-k)) := by conv_lhs => rw [he,pow_add]
    _ = (SourceInfinityOverlap318.u c * inverseU c)^k *
      (SourceInfinityOverlap318.u c)^(N-k) := by rw [mul_pow]; ring
    _ = _ := by rw [ContactWholePrincipalReduction318.u_inverse,one_pow,one_mul]

theorem clear_poleTerm (q : ℚ) (k N : ℕ) (i : ThreeIndex) (hk : k ≤ N) :
    poleTerm c q k i * (SourceInfinityOverlap318.u c)^N =
      InfinityOverlapLocalization318.toOpen c (infinityTerm c q (N-k) i) := by
  rw [inclusion_term]
  calc
    _ = algebraMap ℚ (OverlapRing c) q * ((inverseU c)^k * (SourceInfinityOverlap318.u c)^N) *
      InfinityOverlapLocalization318.toOpen c (ContactHOneOrderBases318.infinityBasis c i) := by
        unfold poleTerm
        ring
    _ = _ := by rw [inverse_lower_mul c k N hk]

theorem clear_negativeSum (q : ℕ → ThreeIndex → ℚ) (N : ℕ) :
    negativeSum c q N * (SourceInfinityOverlap318.u c)^N =
      InfinityOverlapLocalization318.toOpen c (clearedSum c q N) := by
  unfold negativeSum clearedSum
  rw [Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact clear_poleTerm c (q k i) (k+1) N i (by have := Finset.mem_range.mp hk; omega)

/-- Evaluation of the actual coefficient at u=0 isolates the highest pole. -/
theorem highest_coefficient (q : ℕ → ThreeIndex → ℚ) (n : ℕ) (i : ThreeIndex) :
    zeroCoordinate c i (clearedSum c q (n+1)) = q n i := by
  classical
  unfold clearedSum
  rw [map_sum,Finset.sum_eq_single n]
  · simp only [zeroCoordinate_sum_terms,Nat.sub_self,ite_true]
  · intro k hk hkn
    have he : n+1-(k+1) ≠ 0 := by have := Finset.mem_range.mp hk; omega
    rw [zeroCoordinate_sum_terms,if_neg he]
  · simp

theorem highest_zero_of_regular (q : ℕ → ThreeIndex → ℚ) (n : ℕ) (b : InfinityRing c)
    (h : negativeSum c q (n+1) = InfinityOverlapLocalization318.toOpen c b) :
    ∀ i, q n i = 0 := by
  have he := congrArg (fun x : OverlapRing c => x * (SourceInfinityOverlap318.u c)^(n+1)) h
  rw [clear_negativeSum] at he
  have he' : InfinityOverlapLocalization318.toOpen c (clearedSum c q (n+1)) =
      InfinityOverlapLocalization318.toOpen c (b * (coordinate c)^(n+1)) := by
    simpa only [map_mul,map_pow,inclusion_coordinate] using he
  have hh := inclusion_injective c he'
  intro i
  have hi := congrArg (zeroCoordinate c i) hh
  rw [highest_coefficient,zeroCoordinate_mul_coordinate_succ] at hi
  exact hi

theorem negativeSum_succ_of_top_zero (q : ℕ → ThreeIndex → ℚ) (n : ℕ)
    (hq : ∀ i, q n i = 0) : negativeSum c q (n+1) = negativeSum c q n := by
  unfold negativeSum
  rw [Finset.sum_range_succ]
  simp only [hq,poleTerm,map_zero,zero_mul,Finset.sum_const_zero,add_zero]

/-- No nonzero finite combination of original negative-power ratio monomials
can be the image of an element of the whole original infinity ring. -/
theorem negative_coefficients_zero (q : ℕ → ThreeIndex → ℚ) (N : ℕ) (b : InfinityRing c)
    (h : negativeSum c q N = InfinityOverlapLocalization318.toOpen c b) :
    ∀ k, k < N → ∀ i, q k i = 0 := by
  induction N generalizing b with
  | zero => intro k hk; omega
  | succ n ih =>
    have htop := highest_zero_of_regular c q n b h
    have hprev : negativeSum c q n = InfinityOverlapLocalization318.toOpen c b :=
      (negativeSum_succ_of_top_zero c q n htop).symm.trans h
    intro k hk i
    by_cases hkn : k < n
    · exact ih b hprev k hkn i
    · have he : k = n := by omega
      subst k
      exact htop i

end OriginalNegativePoleUniqueness318
