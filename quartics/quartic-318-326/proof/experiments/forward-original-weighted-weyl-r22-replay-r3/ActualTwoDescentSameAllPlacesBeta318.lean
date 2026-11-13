module
public import ActualTwoDescentPrimeFamilyAllPlaces318
public section
noncomputable section
namespace ActualTwoDescentSameAllPlacesBeta318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimeFamilyAllPlaces318 ActualTwoDescentSameSupportLocalPoints318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentSmallPattern318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open ActualTwoDescentFiniteConclusion318
open scoped BigOperators

/-- The SAME produced prime support gives actual all-place beta membership on BOTH twists.
Good primes, every bad support prime,2,3 and real infinity are all genuinely covered. -/
theorem actual_same_all_places_beta (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (qB : BetaIndex d → ℕ)
    (hB : ∀ b, p (some (Sum.inl (Sum.inl b)))=qB b)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N) :
    let β := ∏ b, qB b
    let hb : β ≠ 0 := by intro he; norm_num [he] at hβ
    (retainedBetaClass (β : ℚ) (Nat.cast_ne_zero.mpr hb) ∈
      allPlacesImage ((∏ i, p i : ℕ) : ℚ)
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) C.large)))) ∧
    (retainedBetaClass (β : ℚ) (Nat.cast_ne_zero.mpr hb) ∈
      allPlacesImage ((∏ i, restricted p i : ℕ) : ℚ)
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) C0.large)))) := by
  dsimp only
  letI : ∀ i : Index d, Fact (restricted p i).Prime :=
    fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
  have hmono0 : monomial (restricted p) (beta d)=∏ b, qB b := by
    calc
      monomial (restricted p) (beta d)=∏ b : BetaIndex d, restricted p (bIndex b) := by
        simp [monomial,Fintype.prod_option,Fintype.prod_sum_type,beta,bIndex]
      _=∏ b, qB b := by
        apply Finset.prod_congr rfl
        intro b _
        exact hB b
  have hmono : monomial p (extend (beta d))=∏ b, qB b := by
    rw [actual_extended_monomial,hmono0]
  have hdiv := actual_monomial_divides_product p (extend (beta d))
  have hdiv0 := actual_monomial_divides_product (restricted p) (beta d)
  rw [hmono] at hdiv
  rw [hmono0] at hdiv0
  have hb : (∏ b, qB b) ≠ 0 := by intro he; norm_num [he] at hβ
  obtain ⟨⟨h2,h3,hbad⟩,⟨h20,h30,hbad0⟩⟩ := actual_same_support_beta_points d p hd qB hB hβ N C C0
  exact ⟨actual_family_all_places p _ hb hdiv h2 h3 hbad,
    actual_family_all_places (restricted p) _ hb hdiv0 h20 h30 hbad0⟩

end ActualTwoDescentSameAllPlacesBeta318
