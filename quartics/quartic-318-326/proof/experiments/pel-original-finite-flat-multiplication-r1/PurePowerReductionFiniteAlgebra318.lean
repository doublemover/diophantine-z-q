module
public import PurePowerReductionFiniteSpan318
public import Mathlib.RingTheory.Adjoin.Basic
public section
noncomputable section
namespace PurePowerReductionFiniteAlgebra318
open PurePowerReductionFiniteSpan318
variable {ι R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]

/-- The whole multiplicative closure of the actual generators consists
of the literal monomials, without an unproved polynomial-presentation premise. -/
lemma closure_eq_monomials (x : ι → A) :
    (Submonoid.closure (Set.range x) : Set A) = Set.range (monomial x) := by
  classical
  let S : Submonoid A :=
    { carrier := Set.range (monomial x)
      one_mem' := ⟨0,by simp [monomial]⟩
      mul_mem' := by
        rintro a b ⟨d,rfl⟩ ⟨e,rfl⟩
        exact ⟨d+e,monomial_add x d e⟩ }
  apply Set.Subset.antisymm
  · change Submonoid.closure (Set.range x) ≤ S
    apply Submonoid.closure_le.mpr
    rintro a ⟨i,rfl⟩
    exact ⟨Pi.single i 1,by simp only [monomial_single,pow_one]⟩
  · rintro a ⟨d,rfl⟩
    exact (Submonoid.closure (Set.range x)).prod_mem fun i _ =>
      (Submonoid.closure (Set.range x)).pow_mem (Submonoid.subset_closure ⟨i,rfl⟩) _

/-- Simultaneous degree-reducing pure-power relations make the ACTUAL
whole generated subalgebra finite over its specified base. -/
theorem finite_adjoin (x : ι → A) (N : ι → ℕ)
    (hrel : ∀ i, x i ^ N i ∈ Submodule.span R
      {y : A | ∃ d : ι → ℕ, weight d < N i ∧ monomial x d = y}) :
    Module.Finite R (Algebra.adjoin R (Set.range x)) := by
  apply Module.Finite.of_fg
  change (Algebra.adjoin R (Set.range x)).toSubmodule.FG
  rw [Algebra.adjoin_eq_span,closure_eq_monomials]
  exact fg_span x N hrel

/-- When those generators generate the WHOLE given algebra, the finite
module conclusion concerns that same algebra and its original scalars. -/
theorem finite_whole (x : ι → A) (N : ι → ℕ)
    (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (hrel : ∀ i, x i ^ N i ∈ Submodule.span R
      {y : A | ∃ d : ι → ℕ, weight d < N i ∧ monomial x d = y}) :
    Module.Finite R A := by
  rw [Module.finite_def]
  have hfg := fg_span x N hrel
  have heq : Submodule.span R (Set.range (monomial x)) = ⊤ := by
    rw [←closure_eq_monomials,←Algebra.adjoin_eq_span,hgen]
    rfl
  rwa [heq] at hfg
end PurePowerReductionFiniteAlgebra318
