module
public import FourRootProjectiveProjection318
public import FourRootActualGenericField318
public section
noncomputable section
namespace FourRootCenteredFiniteBase318
open Polynomial FourRootOrder318 FourRootOrderSigns318
open FourRootAffineCoordinateRing318
variable (b:Fin 4→ℂ)
abbrev P:=Polynomial ℂ
@[expose] def radicand (k:Fin 4):P:=X+C (b 0-b k)
abbrev TensorRing:=Order (radicand b)
local instance polyAlgebra:Algebra P (Ring b):=
  (FourRootProjectiveProjection318.finiteCoordinate b).toAlgebra
local instance polyTower:IsScalarTower ℂ P (Ring b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
lemma base_X:algebraMap P (Ring b) X=coordinate b none-algebraMap ℂ (Ring b) (b 0):=
  Polynomial.aeval_X _
lemma base_C (c:ℂ):algebraMap P (Ring b) (C c)=algebraMap ℂ (Ring b) c:=Polynomial.aeval_C _ _

@[expose] def toTensor:Ring b→ₐ[ℂ]TensorRing b:=
  FourRootAffineCoordinateRing318.lift b
    (algebraMap P (TensorRing b) X+algebraMap ℂ (TensorRing b) (b 0))
    (generator (radicand b)) (by
      intro k
      rw [generator_square]
      simp only [radicand,map_add,map_sub,←IsScalarTower.algebraMap_apply]
      ring)
@[simp] theorem toTensor_base:toTensor b (coordinate b none)=
    algebraMap P (TensorRing b) X+algebraMap ℂ (TensorRing b) (b 0):=
  FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _
@[simp] theorem toTensor_root (k:Fin 4):toTensor b (coordinate b (some k))=generator (radicand b) k:=
  FourRootAffineCoordinateRing318.lift_coordinate _ _ _ _ _

@[expose] def fromTensor:TensorRing b→ₐ[P]Ring b:=
  FourRootTensorUniversal318.lift (radicand b) (fun k=>coordinate b (some k)) (by
    intro k
    rw [relation]
    simp only [radicand,map_add,base_X,base_C,map_sub]
    ring)
@[simp] theorem fromTensor_root (k:Fin 4):
    fromTensor b (generator (radicand b) k)=coordinate b (some k):=
  FourRootTensorUniversal318.lift_generator _ _ _ _
lemma fromTensor_base:fromTensor b (algebraMap P (TensorRing b) X)=
    coordinate b none-algebraMap ℂ (Ring b) (b 0):=by rw [AlgHom.commutes,base_X]

@[expose] def equivalence:Ring b≃ₐ[ℂ]TensorRing b:=
  AlgEquiv.ofAlgHom (toTensor b) ((fromTensor b).restrictScalars ℂ)
    (by
      apply AlgHom.toRingHom_injective
      apply FourRootTensorUniversal318.ringHom_ext
      · apply Polynomial.ringHom_ext
        · intro c
          change toTensor b (fromTensor b (algebraMap P (TensorRing b) (C c)))=_
          rw [AlgHom.commutes,base_C,AlgHom.commutes]
          exact (IsScalarTower.algebraMap_apply ℂ P (TensorRing b) c).symm
        · change toTensor b (fromTensor b (algebraMap P (TensorRing b) X))=_
          rw [fromTensor_base,map_sub,toTensor_base,AlgHom.commutes]
          ring
      · intro k
        change toTensor b (fromTensor b (generator (radicand b) k))=_
        rw [fromTensor_root,toTensor_root])
    (by
      apply FourRootAffineCoordinateRing318.hom_ext
      intro k
      cases k with
      | none=>
        change fromTensor b (toTensor b (coordinate b none))=_
        rw [toTensor_base,map_add,fromTensor_base]
        have hc:=((fromTensor b).restrictScalars ℂ).commutes (b 0)
        change fromTensor b (algebraMap ℂ (TensorRing b) (b 0))=_ at hc
        rw [hc]
        ring
      | some k=>
        change fromTensor b (toTensor b (coordinate b (some k)))=_
        rw [toTensor_root,fromTensor_root])

lemma equivalence_base (p:P):equivalence b (algebraMap P (Ring b) p)=algebraMap P (TensorRing b) p:=by
  have he:(toTensor b).toRingHom.comp (algebraMap P (Ring b))=algebraMap P (TensorRing b):=by
    apply Polynomial.ringHom_ext
    · intro c
      change toTensor b (algebraMap P (Ring b) (C c))=_
      rw [base_C,AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply ℂ P (TensorRing b) c).symm
    · change toTensor b (algebraMap P (Ring b) X)=_
      rw [base_X,map_sub,toTensor_base,AlgHom.commutes]
      ring
  exact RingHom.congr_fun he p
@[expose] def polynomialEquivalence:Ring b≃ₐ[P]TensorRing b:=
  {(equivalence b).toRingEquiv with commutes':=equivalence_base b}

/-- Actual centered projection q=t-b0, not a free module for a different
polynomial-base action. All four labeled roots remain unchanged. -/
theorem finite_free:Module.Finite P (Ring b) ∧ Module.Free P (Ring b):=by
  letI:Module.Finite P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).1
  letI:Module.Free P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).2
  exact ⟨Module.Finite.equiv (polynomialEquivalence b).symm.toLinearEquiv,
    Module.Free.of_equiv (polynomialEquivalence b).symm.toLinearEquiv⟩
theorem rank_sixteen:Module.finrank P (Ring b)=16:=by
  rw [(polynomialEquivalence b).toLinearEquiv.finrank_eq]
  exact FourRootOrder318.rank_sixteen _
end FourRootCenteredFiniteBase318
