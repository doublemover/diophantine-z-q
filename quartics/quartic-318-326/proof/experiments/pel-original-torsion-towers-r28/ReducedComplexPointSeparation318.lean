module
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace ReducedComplexPointSeparation318
variable {ι A : Type*} [Finite ι] [CommRing A] [Algebra ℂ A] [IsReduced A]

/-- ALL actual coefficient-preserving complex points separate elements
of a reduced finitely generated complex algebra. The nilpotent step is
explicit; pointwise vanishing is not silently used on a nonreduced ring. -/
theorem eq_zero (φ : MvPolynomial ι ℂ →ₐ[ℂ] A) (hφ : Function.Surjective φ)
    (a : A) (ha : ∀ f : A →ₐ[ℂ] ℂ, f a=0) : a=0 := by
  obtain ⟨p,hp⟩ := hφ a
  let I := RingHom.ker φ.toRingHom
  have hv : p ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    intro v hv
    have hker : RingHom.ker φ.toRingHom ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom :=
      fun q hq => hv q hq
    let f : A →ₐ[ℂ] ℂ := AlgHom.liftOfSurjective φ hφ (MvPolynomial.aeval v) hker
    have he := AlgHom.liftOfSurjective_apply φ hφ (MvPolynomial.aeval v) hker p
    have hz := ha f
    rw [←hp] at hz
    exact he.symm.trans hz
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hv
  obtain ⟨n,hn⟩ := (Ideal.mem_radical_iff).mp hv
  have hnil : IsNilpotent a := by
    refine ⟨n,?_⟩
    change φ (p^n)=0 at hn
    rwa [map_pow,hp] at hn
  exact isNilpotent_iff_eq_zero.mp hnil

theorem ext (φ : MvPolynomial ι ℂ →ₐ[ℂ] A) (hφ : Function.Surjective φ)
    (a b : A) (h : ∀ f : A →ₐ[ℂ] ℂ, f a=f b) : a=b := by
  apply sub_eq_zero.mp
  apply eq_zero φ hφ
  intro f
  rw [map_sub,h f,sub_self]
end ReducedComplexPointSeparation318
