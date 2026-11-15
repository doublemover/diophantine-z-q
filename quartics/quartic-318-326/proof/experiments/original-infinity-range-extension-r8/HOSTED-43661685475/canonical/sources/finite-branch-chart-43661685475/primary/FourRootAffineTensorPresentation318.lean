module
public import FourRootAffineCoordinateRing318
public import FourRootTensorUniversal318
public section
noncomputable section
namespace FourRootAffineTensorPresentation318
open Polynomial FourRootOrder318 FourRootOrderSigns318
open FourRootAffineCoordinateRing318
variable (b:Fin 4→ℂ)
abbrev P:=Polynomial ℂ
@[expose] def radicand (k:Fin 4):P:=X-C (b k)
abbrev TensorRing:=FourRootOrder318.Order (radicand b)

local instance polyAlgebra:Algebra P (Ring b):=
  (Polynomial.aeval (coordinate b none)).toAlgebra
local instance polyTower:IsScalarTower ℂ P (Ring b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm

lemma base_X:algebraMap P (Ring b) X=coordinate b none:=Polynomial.aeval_X _
lemma base_C (c:ℂ):algebraMap P (Ring b) (C c)=algebraMap ℂ (Ring b) c:=Polynomial.aeval_C _ _

@[expose] def toTensor:Ring b→ₐ[ℂ]TensorRing b:=
  FourRootAffineCoordinateRing318.lift b (algebraMap P (TensorRing b) X)
    (generator (radicand b)) (by
      intro k
      rw [generator_square]
      simp only [radicand,map_sub,←IsScalarTower.algebraMap_apply]
      rfl)

@[simp] theorem toTensor_base:toTensor b (coordinate b none)=algebraMap P (TensorRing b) X:=
  FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _
@[simp] theorem toTensor_root (k:Fin 4):toTensor b (coordinate b (some k))=generator (radicand b) k:=
  FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _

@[expose] def fromTensor:TensorRing b→ₐ[P]Ring b:=
  FourRootTensorUniversal318.lift (radicand b) (fun k=>coordinate b (some k)) (by
    intro k
    rw [relation]
    simp only [radicand,map_sub,base_X,base_C])

@[simp] theorem fromTensor_root (k:Fin 4):
    fromTensor b (generator (radicand b) k)=coordinate b (some k):=
  FourRootTensorUniversal318.lift_generator _ _ _ _

lemma fromTensor_base:fromTensor b (algebraMap P (TensorRing b) X)=coordinate b none:=by
  rw [AlgHom.commutes,base_X]

/-- The literal five-variable affine quotient is the actual fourfold
quadratic tensor order over the SAME polynomial base, not merely an
abstract vector space of the same rank. -/
@[expose] def equivalence:Ring b≃ₐ[ℂ]TensorRing b:=
  AlgEquiv.ofAlgHom (toTensor b) ((fromTensor b).restrictScalars ℂ)
    (by
      apply AlgHom.toRingHom_injective
      apply FourRootTensorUniversal318.ringHom_ext
      · apply Polynomial.ringHom_ext
        · intro c
          change toTensor b (fromTensor b (algebraMap P (TensorRing b) (C c)))=
            algebraMap P (TensorRing b) (C c)
          rw [AlgHom.commutes,base_C,AlgHom.commutes]
          exact (IsScalarTower.algebraMap_apply ℂ P (TensorRing b) c).symm
        · change toTensor b (fromTensor b (algebraMap P (TensorRing b) X))=
            algebraMap P (TensorRing b) X
          rw [fromTensor_base,toTensor_base]
      · intro k
        change toTensor b (fromTensor b (generator (radicand b) k))=generator (radicand b) k
        rw [fromTensor_root,toTensor_root])
    (by
      apply FourRootAffineCoordinateRing318.hom_ext
      intro k
      cases k with
      | none=>
        change fromTensor b (toTensor b (coordinate b none))=coordinate b none
        rw [toTensor_base,fromTensor_base]
      | some k=>
        change fromTensor b (toTensor b (coordinate b (some k)))=coordinate b (some k)
        rw [toTensor_root,fromTensor_root])

/-- The polynomial-base structure is retained as an explicit equality. -/
theorem equivalence_base (p:P):equivalence b (algebraMap P (Ring b) p)=
    algebraMap P (TensorRing b) p:=by
  have he:(toTensor b).toRingHom.comp (algebraMap P (Ring b))=algebraMap P (TensorRing b):=by
    apply Polynomial.ringHom_ext
    · intro c
      change toTensor b (algebraMap P (Ring b) (C c))=_
      rw [base_C,AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply ℂ P (TensorRing b) c).symm
    · change toTensor b (algebraMap P (Ring b) X)=_
      rw [base_X,toTensor_base]
  exact RingHom.congr_fun he p
end FourRootAffineTensorPresentation318
