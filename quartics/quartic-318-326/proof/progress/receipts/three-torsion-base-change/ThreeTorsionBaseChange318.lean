module
public import ThreeTorsionCoefficientMap318
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
namespace ThreeTorsionBaseChange318
open Polynomial ThreeTorsionAlgebra318 ThreeTorsionFunctor318 ThreeTorsionCoefficientMap318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type} [CommRing R] [CommRing S] [Algebra R S]
variable [Invertible (3:R)] [Invertible (3:S)] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S

@[expose] def forward : S ⊗[R] Ring A B hD →ₐ[S] Changed (S:=S) A B hD :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (coefficientMap A B hD) (fun _ _=>Commute.all _ _)
@[expose] def backward : Changed (S:=S) A B hD →ₐ[S] S ⊗[R] Ring A B hD :=
  toHom (a A) (a B) (CompletedKernelBaseChange318.mappedDiscriminant A B hD)
    ⟨(Algebra.TensorProduct.includeRight (x A B hD),Algebra.TensorProduct.includeRight (y A B hD)),by
      constructor
      · have hh:=congrArg (Algebra.TensorProduct.includeRight : Ring A B hD →ₐ[R] S ⊗[R] Ring A B hD)
          (x_relation A B hD)
        rw [←Polynomial.aeval_algHom_apply,map_zero] at hh
        change (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R (S ⊗[R] Ring A B hD)) _=0 at hh
        rw [IsScalarTower.algebraMap_eq R S (S ⊗[R] Ring A B hD),←Polynomial.eval₂_map,polynomial_map] at hh
        exact hh
      · have hh:=congrArg (Algebra.TensorProduct.includeRight : Ring A B hD →ₐ[R] S ⊗[R] Ring A B hD)
          (equation A B hD)
        simp only [map_pow,map_add,map_mul,AlgHom.commutes] at hh
        rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] Ring A B hD) A,
          IsScalarTower.algebraMap_apply R S (S ⊗[R] Ring A B hD) B] at hh
        exact hh⟩
@[simp] lemma backward_x : backward (S:=S) A B hD (x _ _ _)=Algebra.TensorProduct.includeRight (x A B hD) := toHom_x _ _ _ _
@[simp] lemma backward_y : backward (S:=S) A B hD (y _ _ _)=Algebra.TensorProduct.includeRight (y A B hD) := toHom_y _ _ _ _
@[simp] lemma forward_includeRight (t:Ring A B hD) : forward (S:=S) A B hD (Algebra.TensorProduct.includeRight t)=
    coefficientMap A B hD t := by
  simp [forward,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]
@[simp] lemma forward_includeLeft (s:S) : forward (S:=S) A B hD
    ((Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] Ring A B hD) s)=algebraMap S _ s := by
  simp [forward,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]

lemma forward_backward : (forward (S:=S) A B hD).comp (backward A B hD)=AlgHom.id S _ := by
  apply hom_ext (a A) (a B) (CompletedKernelBaseChange318.mappedDiscriminant A B hD)
  · simp only [AlgHom.comp_apply,backward_x,forward_includeRight,coefficientMap_x,AlgHom.id_apply]
  · simp only [AlgHom.comp_apply,backward_y,forward_includeRight,coefficientMap_y,AlgHom.id_apply]
lemma backward_forward : (backward (S:=S) A B hD).comp (forward A B hD)=AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply hom_ext A B hD
    · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,coefficientMap_x,backward_x,AlgHom.id_apply]
    · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,coefficientMap_y,backward_y,AlgHom.id_apply]

/-- Arbitrary scalar extension of the original full rank-eight algebra is
exactly the original two-equation algebra with mapped coefficients. -/
@[expose] def equivalence : S ⊗[R] Ring A B hD ≃ₐ[S] Changed (S:=S) A B hD :=
  AlgEquiv.ofAlgHom (forward A B hD) (backward A B hD) (forward_backward A B hD) (backward_forward A B hD)
@[simp] theorem equivalence_x : equivalence (S:=S) A B hD (1 ⊗ₜ[R] x A B hD)=x _ _ _ := by
  change forward (S:=S) A B hD (Algebra.TensorProduct.includeRight (x A B hD))=_
  rw [forward_includeRight,coefficientMap_x]
@[simp] theorem equivalence_y : equivalence (S:=S) A B hD (1 ⊗ₜ[R] y A B hD)=y _ _ _ := by
  change forward (S:=S) A B hD (Algebra.TensorProduct.includeRight (y A B hD))=_
  rw [forward_includeRight,coefficientMap_y]
end ThreeTorsionBaseChange318
