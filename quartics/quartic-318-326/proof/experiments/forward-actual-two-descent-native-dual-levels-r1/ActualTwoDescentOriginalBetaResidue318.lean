module
public import ActualTwoDescentAllBadCardinality318
public section
noncomputable section
namespace ActualTwoDescentOriginalBetaResidue318
open ActualTwoDescentSmallPattern318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentSameSupportLocalPoints318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Both beta monomials are the SAME original beta prime product. The
2-adic square residue is derived from its17mod24 input, not added as a
new local-solvability premise. -/
theorem actual_original_beta_residues (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) (qB : BetaIndex d → ℕ)
    (hB : ∀ b, p (some (Sum.inl (Sum.inl b)))=qB b)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) :
    (monomial p (extend (beta d)) : ZMod 8)=1 ∧
    (monomial (restricted p) (beta d) : ZMod 8)=1 := by
  have hm0 : monomial (restricted p) (beta d)=∏ b, qB b := by
    calc
      monomial (restricted p) (beta d)=∏ b : BetaIndex d, restricted p (bIndex b) := by
        simp [monomial,Fintype.prod_option,Fintype.prod_sum_type,beta,bIndex]
      _=∏ b, qB b := by
        apply Finset.prod_congr rfl
        intro b _
        exact hB b
  have hm : monomial p (extend (beta d))=∏ b, qB b := by
    rw [actual_extended_monomial,hm0]
  have hb8 : ((∏ b, qB b : ℕ) : ZMod 8)=1 := by
    have h := congrArg (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)) hβ
    simpa using h
  exact ⟨by rw [hm]; exact hb8,by rw [hm0]; exact hb8⟩

end ActualTwoDescentOriginalBetaResidue318
