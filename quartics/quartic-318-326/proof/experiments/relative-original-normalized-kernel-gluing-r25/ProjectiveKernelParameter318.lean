module
public import ProjectiveKernelEquations318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace ProjectiveKernelParameter318
open scoped TensorProduct
universe u v
variable (R P Q : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] (d : P →ₗ[R] Q)

@[expose] def ideal : Ideal (ProjectiveSectionParameter318.algebra R P) :=
  Ideal.span (Set.range (ProjectiveKernelEquations318.equation R P Q d))
abbrev algebra := ProjectiveSectionParameter318.algebra R P ⧸ ideal R P Q d
abbrev quotient : ProjectiveSectionParameter318.algebra R P →ₐ[R] algebra R P Q d :=
  Ideal.Quotient.mkₐ R (ideal R P Q d)

lemma equation_zero (φ : Module.Dual R Q) :
    quotient R P Q d (ProjectiveKernelEquations318.equation R P Q d φ)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self φ))

variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]
  (S : Type v) [CommRing S] [Algebra R S]

@[expose] def forward (a : algebra R P Q d →ₐ[R] S) : LinearMap.ker (d.baseChange S) :=
  ⟨ProjectiveSectionParameter318.points R P S (a.comp (quotient R P Q d)),
    (ProjectiveKernelEquations318.equations_iff R P Q d S _).mp
      (fun φ => by change a (quotient R P Q d _)=0; rw [equation_zero,map_zero])⟩

lemma ideal_le_kernel (x : LinearMap.ker (d.baseChange S)) :
    ideal R P Q d ≤ RingHom.ker
      ((ProjectiveSectionParameter318.points R P S).symm x.val).toRingHom := by
  apply Ideal.span_le.mpr
  rintro y ⟨φ,rfl⟩
  change (ProjectiveSectionParameter318.points R P S).symm x.val
    (ProjectiveKernelEquations318.equation R P Q d φ)=0
  have h := (ProjectiveKernelEquations318.equations_iff R P Q d S
    ((ProjectiveSectionParameter318.points R P S).symm x.val)).mpr
    (by rw [Equiv.apply_symm_apply]; exact x.property)
  exact h φ

@[expose] def backward (x : LinearMap.ker (d.baseChange S)) : algebra R P Q d →ₐ[R] S :=
  Ideal.Quotient.liftₐ (ideal R P Q d)
    ((ProjectiveSectionParameter318.points R P S).symm x.val)
    (fun a ha => RingHom.mem_ker.mp (ideal_le_kernel R P Q d S x ha))

lemma backward_comp (x : LinearMap.ker (d.baseChange S)) :
    (backward R P Q d S x).comp (quotient R P Q d) =
      (ProjectiveSectionParameter318.points R P S).symm x.val :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The actual affine quotient represents the kernel of the base-changed differential
on every coefficient algebra, including nonreduced and nonflat tests. -/
@[expose] def points : (algebra R P Q d →ₐ[R] S) ≃ LinearMap.ker (d.baseChange S) where
  toFun := forward R P Q d S
  invFun := backward R P Q d S
  left_inv a := by
    apply Ideal.Quotient.algHom_ext
    rw [backward_comp]
    exact (ProjectiveSectionParameter318.points R P S).symm_apply_apply
      (a.comp (quotient R P Q d))
  right_inv x := by
    apply Subtype.ext
    change ProjectiveSectionParameter318.points R P S
      ((backward R P Q d S x).comp (quotient R P Q d))=x.val
    rw [backward_comp,Equiv.apply_symm_apply]
end ProjectiveKernelParameter318
