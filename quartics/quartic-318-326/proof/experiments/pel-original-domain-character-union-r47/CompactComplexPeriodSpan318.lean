module
public import PELOriginalUniformizedDoubling318
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public section
noncomputable section
namespace CompactComplexPeriodSpan318
open Set ComplexAffineFreeTranslation318
set_option maxHeartbeats 2200000
variable (L : AddSubgroup ℂ) [CompactSpace (Torus L)]

/-- Every real functional annihilating the actual periods descends to the
actual compact quotient. Its range is bounded, hence it must be zero.
No finite-rank or full-span assumption is used. -/
theorem annihilating_functional_zero (f : ℂ →ₗ[ℝ] ℝ)
    (hf : ∀ z∈L,f z=0) (z : ℂ) : f z=0 := by
  have hrel (a b : ℂ) (h : (QuotientAddGroup.mk' L) a=(QuotientAddGroup.mk' L) b) : f a=f b := by
    have hm : a-b∈L := by
      apply (QuotientAddGroup.eq_zero_iff).mp
      change (QuotientAddGroup.mk' L) (a-b)=0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact hf (a-b) hm
  let g : Torus L→ℝ := Quotient.lift f (fun a b h => hrel a b (Quotient.sound h))
  have hg : Continuous g := f.continuous_of_finiteDimensional.quotient_lift _
  have hb : Bornology.IsBounded (range f) := by
    apply (isCompact_range hg).isBounded.subset
    rintro r ⟨a,rfl⟩
    exact ⟨projection L a,rfl⟩
  by_contra hz
  have hs : Function.Surjective f := by
    intro r
    refine ⟨(r/f z) • z,?_⟩
    rw [map_smul,smul_eq_mul]
    exact div_mul_cancel₀ r hz
  rw [range_eq_univ.mpr hs] at hb
  exact NormedSpace.unbounded_univ ℝ ℝ hb

/-- Compactness of C/L forces the original period subgroup to span the
whole REAL complex line. This is actual co-compactness, not a rank guess. -/
theorem real_span_top : Submodule.span ℝ (L : Set ℂ)=⊤ := by
  apply top_unique
  intro z _
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
    (Submodule.span ℝ (L : Set ℂ)) z).mp
  intro f hf
  exact annihilating_functional_zero L f
    (fun a ha => (Submodule.mem_dualAnnihilator f).mp hf a (Submodule.subset_span ha)) z
end CompactComplexPeriodSpan318
