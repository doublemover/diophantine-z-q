module
public import FourRootInfinityCoordinateRing318
public import ThreeRootTensorUniversal318
public section
noncomputable section
namespace FourRootInfinityTensorPresentation318
open Polynomial ThreeRootOrder318 ThreeRootCoordinates318
open FourRootInfinityCoordinateRing318
variable (b:Fin 4→ℂ)
abbrev P:=Polynomial ℂ
@[expose] def radicand (k:Fin 3):P:=1+C (b 0-b k.succ)*X^2
abbrev TensorRing:=ThreeRootOrder318.Order (radicand b)

local instance polyAlgebra:Algebra P (Ring b):=
  (Polynomial.aeval (coordinate b none)).toAlgebra
local instance polyTower:IsScalarTower ℂ P (Ring b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
lemma base_X:algebraMap P (Ring b) X=coordinate b none:=Polynomial.aeval_X _
lemma base_C (c:ℂ):algebraMap P (Ring b) (C c)=algebraMap ℂ (Ring b) c:=Polynomial.aeval_C _ _
@[expose] def root (k:Fin 4):TensorRing b:=Fin.cases 1 (generator (radicand b)) k
lemma root_zero:root b 0=1:=rfl
lemma root_succ (k:Fin 3):root b k.succ=generator (radicand b) k:=rfl

@[expose] def toTensor:Ring b→ₐ[ℂ]TensorRing b:=
  FourRootInfinityCoordinateRing318.lift b (algebraMap P (TensorRing b) X) (root b)
    (root_zero b) (by
      intro k
      refine Fin.cases ?_ (fun j=>?_) k
      · simp [root_zero]
      · rw [root_succ,ThreeRootTensorUniversal318.generator_square]
        simp only [radicand,map_add,map_mul,map_pow,map_one,←IsScalarTower.algebraMap_apply]
        rfl)
@[simp] theorem toTensor_base:toTensor b (coordinate b none)=algebraMap P (TensorRing b) X:=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _
@[simp] theorem toTensor_root (k:Fin 4):toTensor b (coordinate b (some k))=root b k:=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _

@[expose] def fromTensor:TensorRing b→ₐ[P]Ring b:=
  ThreeRootTensorUniversal318.lift (radicand b) (fun k=>coordinate b (some k.succ)) (by
    intro k
    rw [relation]
    simp only [radicand,map_add,map_mul,map_pow,map_one,base_X,base_C])
@[simp] theorem fromTensor_root (k:Fin 3):
    fromTensor b (generator (radicand b) k)=coordinate b (some k.succ):=
  ThreeRootTensorUniversal318.lift_generator _ _ _ _
lemma fromTensor_base:fromTensor b (algebraMap P (TensorRing b) X)=coordinate b none:=by
  rw [AlgHom.commutes,base_X]

/-- The normalized infinity ring is the ENTIRE three-root tensor order.
The s0=1 equation is eliminated algebraically, not by discarding points. -/
@[expose] def equivalence:Ring b≃ₐ[ℂ]TensorRing b:=
  AlgEquiv.ofAlgHom (toTensor b) ((fromTensor b).restrictScalars ℂ)
    (by
      apply AlgHom.toRingHom_injective
      apply ThreeRootCoordinates318.ringHom_ext
      · apply Polynomial.ringHom_ext
        · intro c
          change toTensor b (fromTensor b (algebraMap P (TensorRing b) (C c)))=_
          rw [AlgHom.commutes,base_C,AlgHom.commutes]
          exact (IsScalarTower.algebraMap_apply ℂ P (TensorRing b) c).symm
        · change toTensor b (fromTensor b (algebraMap P (TensorRing b) X))=_
          rw [fromTensor_base,toTensor_base]
      · intro k
        change toTensor b (fromTensor b (generator (radicand b) k))=_
        rw [fromTensor_root,toTensor_root,root_succ])
    (by
      apply FourRootInfinityCoordinateRing318.hom_ext
      intro k
      cases k with
      | none=>
        change fromTensor b (toTensor b (coordinate b none))=coordinate b none
        rw [toTensor_base,fromTensor_base]
      | some k=>
        change fromTensor b (toTensor b (coordinate b (some k)))=coordinate b (some k)
        rw [toTensor_root]
        refine Fin.cases ?_ (fun j=>?_) k
        · rw [root_zero,map_one,zero_relation]
        · rw [root_succ,fromTensor_root])

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

@[expose] def polynomialEquivalence:Ring b≃ₐ[P]TensorRing b:=
  { (equivalence b).toRingEquiv with commutes':=equivalence_base b }

theorem finite_free:Module.Finite P (Ring b) ∧ Module.Free P (Ring b):=by
  letI:Module.Finite P (TensorRing b):=(ThreeRootOrder318.finite_free (radicand b)).1
  letI:Module.Free P (TensorRing b):=(ThreeRootOrder318.finite_free (radicand b)).2
  exact ⟨Module.Finite.equiv (polynomialEquivalence b).symm.toLinearEquiv,
    Module.Free.of_equiv (polynomialEquivalence b).symm.toLinearEquiv⟩
theorem rank_eight:Module.finrank P (Ring b)=8:=by
  rw [(polynomialEquivalence b).toLinearEquiv.finrank_eq]
  exact ThreeRootOrder318.rank_eight _
end FourRootInfinityTensorPresentation318
