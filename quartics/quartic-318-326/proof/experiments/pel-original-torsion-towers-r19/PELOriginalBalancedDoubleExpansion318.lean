module
public import PELOriginalBalancedPowerSections318
public import PELOriginalLevelThetaNegation318
public import PELOriginalWholeSectionSpanning318
public import FiniteSeparateFunctionExpansion318
public section
noncomputable section
namespace PELOriginalBalancedDoubleExpansion318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalBalancedPowerSections318 PELOriginalPowerSectionDescent318
open PELOriginalWholeSectionSpanning318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (2*N)]
@[expose] def paired (i j : Label N) (z a : ComplexVectors) : ℂ :=
  value τ hτ N i (z+a)*value τ hτ N j (z-a)
lemma first_span (i j : Label N) (a : ComplexVectors) :
    ∃ c : Label (2*N) → ℂ,∀ z,paired τ hτ N i j z a=
      ∑ k : Label (2*N),c k*value τ hτ (2*N) k z := by
  let f := balancedTheta τ hτ N a i j
  refine ⟨coordinates τ hτ (2*N) (descend τ hτ (2*N) f),?_⟩
  intro z
  have h := original_lift_expansion τ hτ (2*N) (descend τ hτ (2*N) f) z
  rw [lift_descend] at h
  exact h
lemma swap (i j : Label N) (z a : ComplexVectors) :
    paired τ hτ N i j z a=paired τ hτ N i (-j) a z := by
  have h : z-a= -(a-z) := by abel
  simp only [paired,h,PELOriginalLevelThetaNegation318.value_neg,add_comm]
lemma second_span (i j : Label N) (z : ComplexVectors) :
    ∃ c : Label (2*N) → ℂ,∀ a,paired τ hτ N i j z a=
      ∑ k : Label (2*N),c k*value τ hτ (2*N) k a := by
  obtain ⟨c,hc⟩ := first_span τ hτ N i (-j) z
  exact ⟨c,fun a => (swap τ hτ N i j z a).trans (hc a)⟩
/-- Literal constant coefficients for BOTH variables, preserving the
negated characteristic in the second-variable spanning argument. -/
lemma exists_coefficients (i j : Label N) :
    ∃ C : Label (2*N) → Label (2*N) → ℂ,∀ z a,
      paired τ hτ N i j z a=
        ∑ u : Label (2*N),∑ v : Label (2*N),C u v*value τ hτ (2*N) u z*value τ hτ (2*N) v a :=
  FiniteSeparateFunctionExpansion318.exists_double_expansion
    (value τ hτ (2*N)) (value τ hτ (2*N)) (original_values_independent τ hτ (2*N))
    (paired τ hτ N i j) (first_span τ hτ N i j) (second_span τ hτ N i j)
@[expose] def coefficients (i j : Label N) : Label (2*N) → Label (2*N) → ℂ :=
  (exists_coefficients τ hτ N i j).choose
lemma formula (i j : Label N) (z a : ComplexVectors) :
    paired τ hτ N i j z a=
      ∑ u : Label (2*N),∑ v : Label (2*N),coefficients τ hτ N i j u v*
        value τ hτ (2*N) u z*value τ hτ (2*N) v a :=
  (exists_coefficients τ hτ N i j).choose_spec z a
end PELOriginalBalancedDoubleExpansion318
