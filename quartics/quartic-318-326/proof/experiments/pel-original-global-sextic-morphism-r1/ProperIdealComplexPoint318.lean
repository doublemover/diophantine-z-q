module
public import Mathlib.RingTheory.Nullstellensatz
public section
noncomputable section
namespace ProperIdealComplexPoint318
variable {ι A : Type*} [Finite ι] [CommRing A] [Algebra ℂ A]

/-- Every proper ideal in an actual finitely generated complex algebra
is killed by a genuine complex ALGEBRA evaluation. Constants are fixed;
an arbitrary abstract field embedding is not substituted. -/
theorem exists_point (φ : MvPolynomial ι ℂ →ₐ[ℂ] A)
    (hφ : Function.Surjective φ) (I : Ideal A) (hI : I ≠ ⊤) :
    ∃ f : A →ₐ[ℂ] ℂ, ∀ a ∈ I, f a = 0 := by
  obtain ⟨m,hm,hIm⟩ := Ideal.exists_le_maximal I hI
  letI : m.IsMaximal := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let q : A →ₐ[ℂ] A ⧸ m := Ideal.Quotient.mkₐ ℂ m
  let g : MvPolynomial ι ℂ →+* A ⧸ m := (q.comp φ).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hC : g.comp MvPolynomial.C = algebraMap ℂ (A ⧸ m) := by
    ext c
    exact (q.comp φ).commutes c
  letI : Algebra.IsAlgebraic ℂ (A ⧸ m) := by
    rw [Algebra.isAlgebraic_iff_isIntegral,←algebraMap_isIntegral_iff]
    rw [←hC]
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing g hg
  let ψ : A ⧸ m →ₐ[ℂ] ℂ := IsAlgClosed.lift
  refine ⟨ψ.comp q,?_⟩
  intro a ha
  have hz : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIm ha)
  change ψ (q a) = 0
  rw [hz,map_zero]
end ProperIdealComplexPoint318
