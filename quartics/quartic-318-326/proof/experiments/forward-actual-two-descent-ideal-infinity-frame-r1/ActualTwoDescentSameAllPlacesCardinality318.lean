module
public import ActualTwoDescentAllPlacesExactCardinality318
public section
noncomputable section
namespace ActualTwoDescentSameAllPlacesCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentAllPlacesExactCardinality318 ActualTwoDescentSameAllPlacesBeta318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentSameSupportLocalPoints318
open ActualTwoDescentSmallPattern318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentSimultaneousLocalClasses318 ActualTwoDescentAllPlacesIntersection318
open scoped BigOperators

/-- Both actual all-place groups have eight elements on the SAME final support. -/
theorem actual_same_all_places_cardinality (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (qB : BetaIndex d → ℕ)
    (hB : ∀ b, p (some (Sum.inl (Sum.inl b)))=qB b)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N)
    (hn : (∏ i, p i) ≠ 0) (hn0 : (∏ i, restricted p i) ≠ 0) :
    Nat.card (allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn))=8 ∧
    Nat.card (allPlacesImage ((∏ i, restricted p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn0))=8 := by
  letI : ∀ i : Index d, Fact (restricted p i).Prime :=
    fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
  have hemb : Function.Injective (oldEmbedding : Index d → Option (CoreIndex d ⊕ J)) := by
    intro i j he
    cases i <;> cases j <;> simp_all [oldEmbedding]
  have hmono0 : monomial (restricted p) (beta d)=∏ b, qB b := by
    calc
      monomial (restricted p) (beta d)=∏ b : BetaIndex d, restricted p (bIndex b) := by
        simp [monomial,Fintype.prod_option,Fintype.prod_sum_type,beta,bIndex]
      _=∏ b, qB b := by
        apply Finset.prod_congr rfl
        intro b _
        exact hB b
  have hmono : monomial p (extend (beta d))=∏ b, qB b := by rw [actual_extended_monomial,hmono0]
  have hloc := actual_same_all_places_beta d p hd qB hB hβ N C C0
  dsimp only at hloc
  have hc := actual_conclusion_coprime p _ _ N C
  have hp2 : ∀ i, p i ≠ 2 := by
    intro i he; have h := hc i; rw [he] at h; norm_num at h
  have hp3 : ∀ i, p i ≠ 3 := by
    intro i he; have h := hc i; rw [he] at h; norm_num at h
  constructor
  · apply actual_all_places_card_eight p hd hp2 hp3 _ _ N C none (some (Sum.inl (Sum.inl none))) rfl rfl hn
    simpa only [hmono] using hloc.1
  · apply actual_all_places_card_eight (restricted p) (hd.comp hemb)
      (fun i => hp2 (oldEmbedding i)) (fun i => hp3 (oldEmbedding i)) _ _ N C0 none (bIndex none) rfl rfl hn0
    simpa only [hmono0] using hloc.2

end ActualTwoDescentSameAllPlacesCardinality318
