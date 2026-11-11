module
public import FourRootCenteredFiniteBase318
public import FourRootInfinityTensorPresentation318
public section
noncomputable section
namespace FourRootSquaredInfinityBase318
open Polynomial FourRootOrder318 FourRootOrderSigns318
open FourRootInfinityCoordinateRing318
variable (b:Fin 4→ℂ)
abbrev P:=Polynomial ℂ
/-- The first actual root is u with square v; the other three are the
normalized signed ratios with squares1+(b0-bi)v. -/
@[expose] def radicand:Fin 4→P:=
  Fin.cases X (fun k=>1+C (b 0-b k.succ)*X)
abbrev TensorRing:=Order (radicand b)
local instance polyAlgebra:Algebra P (Ring b):=
  (FourRootProjectiveProjection318.infinityCoordinate b).toAlgebra
local instance polyTower:IsScalarTower ℂ P (Ring b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
lemma base_X:algebraMap P (Ring b) X=coordinate b none^2:=Polynomial.aeval_X _
lemma base_C (c:ℂ):algebraMap P (Ring b) (C c)=algebraMap ℂ (Ring b) c:=Polynomial.aeval_C _ _
@[expose] def ratio:Fin 4→TensorRing b:=Fin.cases 1 (fun k=>generator (radicand b) k.succ)
@[expose] def originalRoot:Fin 4→Ring b:=Fin.cases (coordinate b none) (fun k=>coordinate b (some k.succ))

@[expose] def toTensor:Ring b→ₐ[ℂ]TensorRing b:=
  FourRootInfinityCoordinateRing318.lift b (generator (radicand b) 0) (ratio b) rfl (by
    intro k
    refine Fin.cases ?_ (fun j=>?_) k
    · simp [ratio]
    · change generator (radicand b) j.succ^2=1+
        algebraMap ℂ (TensorRing b) (b 0-b j.succ)*generator (radicand b) 0^2
      rw [generator_square,generator_square]
      simp only [radicand,Fin.cases_succ,Fin.cases_zero,map_add,map_mul,map_one,
        ←IsScalarTower.algebraMap_apply]
      rfl)
@[simp] theorem toTensor_base:toTensor b (coordinate b none)=generator (radicand b) 0:=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _
@[simp] theorem toTensor_ratio (k:Fin 4):toTensor b (coordinate b (some k))=ratio b k:=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _

@[expose] def fromTensor:TensorRing b→ₐ[P]Ring b:=
  FourRootTensorUniversal318.lift (radicand b) (originalRoot b) (by
    intro k
    refine Fin.cases ?_ (fun j=>?_) k
    · change coordinate b none^2=algebraMap P (Ring b) X
      exact (base_X b).symm
    · change coordinate b (some j.succ)^2=algebraMap P (Ring b) (1+C (b 0-b j.succ)*X)
      rw [relation]
      simp only [map_add,map_mul,map_one,base_C,base_X])
@[simp] theorem fromTensor_root (k:Fin 4):
    fromTensor b (generator (radicand b) k)=originalRoot b k:=
  FourRootTensorUniversal318.lift_generator _ _ _ _
lemma fromTensor_base:fromTensor b (algebraMap P (TensorRing b) X)=coordinate b none^2:=by
  rw [AlgHom.commutes,base_X]

/-- This is the entire infinity ring over the actual projective reciprocal
coordinate v=u², not its rank8 presentation over the different u-base. -/
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
          rw [fromTensor_base,map_pow,toTensor_base,generator_square]
          rfl
      · intro k
        change toTensor b (fromTensor b (generator (radicand b) k))=_
        rw [fromTensor_root]
        refine Fin.cases ?_ (fun j=>?_) k
        · exact toTensor_base b
        · exact toTensor_ratio b j.succ)
    (by
      apply FourRootInfinityCoordinateRing318.hom_ext
      intro k
      cases k with
      | none=>
        change fromTensor b (toTensor b (coordinate b none))=_
        rw [toTensor_base,fromTensor_root]
        rfl
      | some k=>
        change fromTensor b (toTensor b (coordinate b (some k)))=_
        rw [toTensor_ratio]
        refine Fin.cases ?_ (fun j=>?_) k
        · change fromTensor b 1=coordinate b (some 0)
          rw [map_one,zero_relation]
        · exact fromTensor_root b j.succ)

lemma equivalence_base (p:P):equivalence b (algebraMap P (Ring b) p)=algebraMap P (TensorRing b) p:=by
  have he:(toTensor b).toRingHom.comp (algebraMap P (Ring b))=algebraMap P (TensorRing b):=by
    apply Polynomial.ringHom_ext
    · intro c
      change toTensor b (algebraMap P (Ring b) (C c))=_
      rw [base_C,AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply ℂ P (TensorRing b) c).symm
    · change toTensor b (algebraMap P (Ring b) X)=_
      rw [base_X,map_pow,toTensor_base,generator_square]
      rfl
  exact RingHom.congr_fun he p
@[expose] def polynomialEquivalence:Ring b≃ₐ[P]TensorRing b:=
  {(equivalence b).toRingEquiv with commutes':=equivalence_base b}

theorem finite_free:Module.Finite P (Ring b) ∧ Module.Free P (Ring b):=by
  letI:Module.Finite P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).1
  letI:Module.Free P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).2
  exact ⟨Module.Finite.equiv (polynomialEquivalence b).symm.toLinearEquiv,
    Module.Free.of_equiv (polynomialEquivalence b).symm.toLinearEquiv⟩
theorem rank_sixteen:Module.finrank P (Ring b)=16:=by
  rw [(polynomialEquivalence b).toLinearEquiv.finrank_eq]
  exact FourRootOrder318.rank_sixteen _
end FourRootSquaredInfinityBase318
