module
public import ActualTwoDescentBetaSupportPoints318
public section
noncomputable section
namespace ActualTwoDescentSameSupportLocalPoints318
open ActualTwoDescentBetaSupportPoints318 ActualTwoDescentExceptionalLocalPoints318
open ActualTwoDescentLocalKummerWitness318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentSmallPattern318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentSimultaneousLocalClasses318
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual_extended_monomial {U J : Type*} [Fintype U] [DecidableEq U]
    [Fintype J] [DecidableEq J] (p : Option (U ⊕ J) → ℕ) (b : Option U → ZMod 2) :
    monomial p (extend b)=monomial (restricted p) b := by
  simp only [monomial,Fintype.prod_option,Fintype.prod_sum_type,extend,restricted,oldEmbedding,
    ZMod.val_zero,pow_zero,Finset.prod_const_one,mul_one]

/-- This consumer keeps the exact final prime support and original beta
product. It supplies actual beta-class local curve points at2,3 and EVERY
support prime for BOTH n and nθ. Good-prime sufficiency and the global
rational-point step are still separate, not hidden in this statement. -/
theorem actual_same_support_beta_points (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (qB : BetaIndex d → ℕ)
    (hB : ∀ b, p (some (Sum.inl (Sum.inl b)))=qB b)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N) :
    (Nonempty (LocalKummerPoint (p:=2) (∏ b, qB b) (∏ i, p i)) ∧
      Nonempty (LocalKummerPoint (p:=3) (∏ b, qB b) (∏ i, p i)) ∧
      ∀ i, Nonempty (LocalKummerPoint (p:=p i) (∏ b, qB b) (∏ j, p j))) ∧
    (Nonempty (LocalKummerPoint (p:=2) (∏ b, qB b) (∏ i, restricted p i)) ∧
      Nonempty (LocalKummerPoint (p:=3) (∏ b, qB b) (∏ i, restricted p i)) ∧
      ∀ i : Index d, Nonempty (LocalKummerPoint (p:=p (oldEmbedding i))
        (∏ b, qB b) (∏ j, restricted p j))) := by
  letI : ∀ i : Index d, Fact (restricted p i).Prime :=
    fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
  have hemb : Function.Injective (oldEmbedding : Index d → Option (CoreIndex d ⊕ J)) := by
    intro i j he
    cases i <;> cases j <;> simp_all [oldEmbedding]
  have hd0 : Function.Injective (restricted p) := hd.comp hemb
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
  have hc := actual_conclusion_coprime p _ _ N C
  have hp2 : ∀ i, p i ≠ 2 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hp20 : ∀ i : Index d, restricted p i ≠ 2 := fun i => hp2 (oldEmbedding i)
  have hn0 : (∏ i, p i) ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) C.large)
  have hn00 : (∏ i, restricted p i) ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) C0.large)
  have hbad := actual_beta_support_points p hd hp2 (extend (beta d)) C.beta_kernel
  have hbad0 := actual_beta_support_points (restricted p) hd0 hp20 (beta d) C0.beta_kernel
  rw [hmono] at hbad
  rw [hmono0] at hbad0
  exact ⟨⟨actual_two_adic_kummer_point _ _ hβ,
    actual_three_adic_kummer_point _ _ hn0 hβ C.residue,hbad⟩,
    ⟨actual_two_adic_kummer_point _ _ hβ,
    actual_three_adic_kummer_point _ _ hn00 hβ C0.residue,hbad0⟩⟩

end ActualTwoDescentSameSupportLocalPoints318
