module
public import CanonicalJacobiTrace318
public section
noncomputable section
namespace CanonicalQuarticCharacter318
open CanonicalJacobiTrace318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Produce an actual quartic character by sending a generator of the
finite field unit group to i. Its square is the actual quadratic character. -/
theorem exists_quartic (hF : ringChar F≠2) (h4 : 4∣Fintype.card F-1) :
    ∃ ψ : MulChar F ℂ, ψ^2=quadraticComplex ∧ ψ^4=1 := by
  obtain ⟨g,hg⟩ := (inferInstance : IsCyclic Fˣ).exists_generator
  let z : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have hI : Complex.I^4=1 := by norm_num [pow_succ]
  have hz : z∈rootsOfUnity (Fintype.card Fˣ) ℂ := by
    apply (mem_rootsOfUnity _ _).mpr
    apply Units.ext
    change Complex.I^(Fintype.card Fˣ)=1
    rw [Fintype.card_units]
    obtain ⟨k,hk⟩ := h4
    rw [hk,pow_mul,hI,one_pow]
  let ψ : MulChar F ℂ := MulChar.ofRootOfUnity hz hg
  have hψ : ψ (g:F)=Complex.I := MulChar.ofRootOfUnity_spec hz hg
  have hχne : quadraticComplex (g:F)≠1 := by
    intro he
    have hall : (quadraticChar F)=1 := by
      apply (MulChar.eq_iff hg _ _).mpr
      have hi : quadraticChar F (g:F)=1 := by
        have he' : (quadraticChar F (g:F):ℂ)=1 := he
        exact_mod_cast he'
      rw [hi,MulChar.one_apply g.isUnit]
    exact quadraticChar_ne_one hF hall
  have hχ : quadraticComplex (g:F)= -1 := by
    rcases quadraticChar_dichotomy (show (g:F)≠0 from Units.ne_zero g) with h|h
    · exfalso
      apply hχne
      rw [quadraticComplex_apply,h]; norm_num
    · rw [quadraticComplex_apply,h]; norm_num
  refine ⟨ψ,?_,?_⟩
  · apply (MulChar.eq_iff hg _ _).mpr
    rw [MulChar.pow_apply_coe,hψ,hχ,Complex.I_sq]
  · apply (MulChar.eq_iff hg _ _).mpr
    rw [MulChar.pow_apply_coe,hψ,hI,MulChar.one_apply g.isUnit]

end CanonicalQuarticCharacter318
