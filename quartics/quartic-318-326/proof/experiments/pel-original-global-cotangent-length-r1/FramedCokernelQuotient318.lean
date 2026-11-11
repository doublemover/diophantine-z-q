module
public import FramedMorphismCoefficientAssociates318
public import Mathlib.LinearAlgebra.Quotient.Basic
public section
noncomputable section
namespace FramedCokernelQuotient318
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]
  (e : R ≃ₗ[R] M) (f : R ≃ₗ[R] N) (d : M →ₗ[R] N)

lemma action (x : M) : f.symm (d x) = e.symm x * f.symm (d (e 1)) := by
  have hx : x = (e.symm x) • e 1 := by
    rw [←e.map_smul,smul_eq_mul,mul_one,e.apply_symm_apply]
  rw [hx,map_smul,map_smul,smul_eq_mul]

/-- Full image submodule under an actual target frame, including all
multiplicities. This is not an annihilator or support comparison. -/
lemma range_map : (LinearMap.range d).map f.symm.toLinearMap =
    Ideal.span {f.symm (d (e 1))} := by
  ext y
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    rw [action e f d]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · intro hy
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨d (e r),⟨e r,rfl⟩,?_⟩
    rw [action e f d,LinearEquiv.symm_apply_apply]
    exact hr

/-- Actual generator units and actual image equation identify the
cokernel quotient with the literal coefficient ideal quotient. -/
@[expose] def quotientEquiv (s : M) (t : N) (a : R)
    (h : d s = a • t) (hs : IsUnit (e.symm s)) (ht : IsUnit (f.symm t)) :
    (N ⧸ LinearMap.range d) ≃ₗ[R] R ⧸ Ideal.span {a} :=
  Submodule.Quotient.equiv _ _ f.symm
    ((range_map e f d).trans (FramedMorphismCoefficientAssociates318.span_eq e f d s t a h hs ht))
end FramedCokernelQuotient318
