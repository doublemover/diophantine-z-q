module
public import SquareZeroProjectiveGenerator318
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace SurjectiveScalarReduction318
open scoped TensorProduct Pointwise
universe u v w
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {R : Type v} [CommRing S] [CommRing R] [Algebra S R]
    (hπ : Function.Surjective (algebraMap S R))
    (P : Type w) [AddCommGroup P] [Module S P]
@[expose] def residueEquiv : (S ⧸ RingHom.ker (algebraMap S R)) ≃ₐ[S] R :=
  Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S R) hπ
/-- The genuine scalar-extension quotient theorem for the actual reduction map. -/
@[expose] def quotientEquiv : R ⊗[S] P ≃ₗ[S]
    P ⧸ ((RingHom.ker (algebraMap S R)) • (⊤ : Submodule S P)) :=
  TensorProduct.congr (residueEquiv hπ).symm.toLinearEquiv (LinearEquiv.refl S P) ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMul P (RingHom.ker (algebraMap S R))
@[expose] def reduce : P →ₗ[S] R ⊗[S] P := TensorProduct.mk S R P 1
lemma quotientEquiv_reduce (x : P) :
    quotientEquiv hπ P (reduce P x) = Submodule.Quotient.mk x := by
  change TensorProduct.quotTensorEquivQuotSMul P (RingHom.ker (algebraMap S R))
    ((residueEquiv hπ).symm 1 ⊗ₜ[S] x) = _
  rw [map_one, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
include hπ in
lemma reduce_surjective : Function.Surjective (reduce (S := S) (R := R) P) := by
  intro y
  obtain ⟨x,hx⟩ := Submodule.mkQ_surjective
    ((RingHom.ker (algebraMap S R)) • (⊤ : Submodule S P)) (quotientEquiv hπ P y)
  refine ⟨x, (quotientEquiv hπ P).injective ?_⟩
  rw [quotientEquiv_reduce]
  exact hx
include hπ in
lemma reduce_zero_iff (x : P) :
    reduce (S := S) (R := R) P x = 0 ↔
      x ∈ (RingHom.ker (algebraMap S R)) • (⊤ : Submodule S P) := by
  rw [← (quotientEquiv hπ P).map_eq_zero_iff, quotientEquiv_reduce, Submodule.Quotient.mk_eq_zero]
variable (e : S) (hker : RingHom.ker (algebraMap S R) = Ideal.span {e})
include hπ hker in
lemma epsilon_kernel (x : P) (hx : reduce (S := S) (R := R) P x = 0) :
    ∃ y : P, e • y = x := by
  have hm := (reduce_zero_iff hπ P x).1 hx
  rw [hker, Submodule.ideal_span_singleton_smul] at hm
  obtain ⟨y,_,hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
  exact ⟨y,hy⟩
end SurjectiveScalarReduction318
