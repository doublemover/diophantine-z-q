module
public import ActualTwoDescentRationalEightClasses318
public section
noncomputable section
namespace ActualTwoDescentSameRationalBounds318
open ActualTwoDescentRationalEightClasses318 ActualTwoDescentRationalPointPlaces318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentSmallPattern318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentSameSupportLocalPoints318
open ActualTwoDescentSimultaneousLocalClasses318
open scoped BigOperators
set_option maxHeartbeats 16000000

def RationalEightBound (n beta : ℕ) : Prop :=
  ∀ P : RationalPoint n, ∃ ε c e : ZMod 2, ∃ r s : ℚ, r ≠ 0 ∧ s ≠ 0 ∧
    P.x+3*n=(3 : ℚ)^ε.val*(n : ℚ)^c.val*(beta : ℚ)^e.val*r^2 ∧
    P.x-n=(- (n : ℚ))^ε.val*s^2

/-- The same ORIGINAL beta bounds the actual rational Kummer classes on
BOTH final twists. Every point is normalized from its actual valuations;
no supported-representative or local-image assumption remains. -/
theorem actual_same_rational_bounds (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (qB : BetaIndex d → ℕ)
    (hB : ∀ b, p (some (Sum.inl (Sum.inl b)))=qB b) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N) :
    RationalEightBound (∏ i, p i) (∏ b, qB b) ∧
    RationalEightBound (∏ i, restricted p i) (∏ b, qB b) := by
  letI : ∀ i : Index d, Fact (restricted p i).Prime :=
    fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
  have hemb : Function.Injective (oldEmbedding : Index d → Option (CoreIndex d ⊕ J)) := by
    intro i j he
    cases i <;> cases j <;> simp_all [oldEmbedding]
  have hm0 : monomial (restricted p) (beta d)=∏ b, qB b := by
    calc
      monomial (restricted p) (beta d)=∏ b : BetaIndex d, restricted p (bIndex b) := by
        simp [monomial,Fintype.prod_option,Fintype.prod_sum_type,beta,bIndex]
      _=∏ b, qB b := by
        apply Finset.prod_congr rfl
        intro b _
        exact hB b
  have hm : monomial p (extend (beta d))=∏ b, qB b := by rw [actual_extended_monomial,hm0]
  have hc := actual_conclusion_coprime p _ _ N C
  have hp2 : ∀ i, p i ≠ 2 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hp3 : ∀ i, p i ≠ 3 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  constructor
  · intro P
    simpa only [hm] using actual_rational_eight_classes p hd hp2 hp3 _ _ N C P
  · intro P
    simpa only [hm0] using actual_rational_eight_classes (restricted p) (hd.comp hemb)
      (fun i => hp2 (oldEmbedding i)) (fun i => hp3 (oldEmbedding i)) _ _ N C0 P

end ActualTwoDescentSameRationalBounds318
