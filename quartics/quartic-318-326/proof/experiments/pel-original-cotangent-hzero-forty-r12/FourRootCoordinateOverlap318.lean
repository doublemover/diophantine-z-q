module
public import FourRootInfinityCoordinateRing318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace FourRootCoordinateOverlap318
open Algebra
variable (b:Fin 4→ℂ)
abbrev Affine:=FourRootAffineCoordinateRing318.Ring b
abbrev Infinity:=FourRootInfinityCoordinateRing318.Ring b
abbrev AffineOverlap:=Localization.Away (FourRootAffineCoordinateRing318.coordinate b (some 0))
abbrev InfinityOverlap:=Localization.Away (FourRootInfinityCoordinateRing318.coordinate b none)
@[expose] def t:AffineOverlap b:=algebraMap (Affine b) _ (FourRootAffineCoordinateRing318.coordinate b none)
@[expose] def z (k:Fin 4):AffineOverlap b:=algebraMap (Affine b) _ (FourRootAffineCoordinateRing318.coordinate b (some k))
@[expose] def zi:AffineOverlap b:=IsLocalization.Away.invSelf (FourRootAffineCoordinateRing318.coordinate b (some 0))
@[expose] def u:InfinityOverlap b:=algebraMap (Infinity b) _ (FourRootInfinityCoordinateRing318.coordinate b none)
@[expose] def s (k:Fin 4):InfinityOverlap b:=algebraMap (Infinity b) _ (FourRootInfinityCoordinateRing318.coordinate b (some k))
@[expose] def ui:InfinityOverlap b:=IsLocalization.Away.invSelf (FourRootInfinityCoordinateRing318.coordinate b none)
@[simp] lemma z_zi:z b 0*zi b=1:=IsLocalization.Away.mul_invSelf _
@[simp] lemma u_ui:u b*ui b=1:=IsLocalization.Away.mul_invSelf _
@[simp] lemma s_zero:s b 0=1:=by
  change algebraMap (Infinity b) _ (FourRootInfinityCoordinateRing318.coordinate b (some 0))=1
  rw [FourRootInfinityCoordinateRing318.zero_relation,map_one]
lemma finite_relation (k:Fin 4):z b k^2=t b-algebraMap ℂ (AffineOverlap b) (b k):=by
  have h:=congrArg (algebraMap (Affine b) (AffineOverlap b)) (FourRootAffineCoordinateRing318.relation b k)
  simpa only [map_pow,map_sub,←IsScalarTower.algebraMap_apply,z,t] using h
lemma infinity_relation (k:Fin 4):s b k^2=1+algebraMap ℂ (InfinityOverlap b) (b 0-b k)*u b^2:=by
  have h:=congrArg (algebraMap (Infinity b) (InfinityOverlap b)) (FourRootInfinityCoordinateRing318.relation b k)
  simpa only [map_pow,map_add,map_mul,map_one,←IsScalarTower.algebraMap_apply,s,u] using h

/-- The literal normalized infinity equations evaluated in the ACTUAL
finite localization. All roots and the distinguished zeroth ratio remain. -/
@[expose] def toAffineBase:Infinity b→ₐ[ℂ]AffineOverlap b:=
  FourRootInfinityCoordinateRing318.lift b (zi b) (fun k=>z b k*zi b) (z_zi b) (by
    intro k
    rw [mul_pow,finite_relation,map_sub]
    calc
      (t b-algebraMap ℂ (AffineOverlap b) (b k))*zi b^2=
          (t b-algebraMap ℂ (AffineOverlap b) (b 0))*zi b^2+
            (algebraMap ℂ (AffineOverlap b) (b 0)-algebraMap ℂ (AffineOverlap b) (b k))*zi b^2:=by ring
      _=z b 0^2*zi b^2+_=by rw [finite_relation]
      _=1+_:=by rw [←mul_pow,z_zi];norm_num)
/-- Exact inverse equations t=b0+u^-2 and z_k=s_k/u, not just projected
base agreement. No passage to a field or radical ideal occurs. -/
@[expose] def toInfinityBase:Affine b→ₐ[ℂ]InfinityOverlap b:=
  FourRootAffineCoordinateRing318.lift b
    (algebraMap ℂ (InfinityOverlap b) (b 0)+ui b^2) (fun k=>s b k*ui b) (by
      intro k
      rw [mul_pow,infinity_relation,map_sub]
      calc
        (1+(algebraMap ℂ (InfinityOverlap b) (b 0)-algebraMap ℂ (InfinityOverlap b) (b k))*u b^2)*ui b^2=
            ui b^2+(algebraMap ℂ (InfinityOverlap b) (b 0)-algebraMap ℂ (InfinityOverlap b) (b k))*(u b*ui b)^2:=by ring
        _=algebraMap ℂ (InfinityOverlap b) (b 0)+ui b^2-algebraMap ℂ (InfinityOverlap b) (b k):=by
          rw [u_ui];ring)
@[simp] lemma toAffineBase_u:toAffineBase b (FourRootInfinityCoordinateRing318.coordinate b none)=zi b:=
  FourRootInfinityCoordinateRing318.lift_coordinate ..
@[simp] lemma toAffineBase_s (k:Fin 4):toAffineBase b (FourRootInfinityCoordinateRing318.coordinate b (some k))=z b k*zi b:=
  FourRootInfinityCoordinateRing318.lift_coordinate ..
@[simp] lemma toInfinityBase_t:toInfinityBase b (FourRootAffineCoordinateRing318.coordinate b none)=
    algebraMap ℂ (InfinityOverlap b) (b 0)+ui b^2:=FourRootAffineCoordinateRing318.lift_coordinate ..
@[simp] lemma toInfinityBase_z (k:Fin 4):toInfinityBase b (FourRootAffineCoordinateRing318.coordinate b (some k))=s b k*ui b:=
  FourRootAffineCoordinateRing318.lift_coordinate ..
@[expose] def toAffine:InfinityOverlap b→ₐ[ℂ]AffineOverlap b:=
  IsLocalization.Away.liftAlgHom (f:=toAffineBase b) (FourRootInfinityCoordinateRing318.coordinate b none) (by
    rw [toAffineBase_u]
    exact IsUnit.of_mul_eq_one_right _ (z_zi b))
@[expose] def toInfinity:AffineOverlap b→ₐ[ℂ]InfinityOverlap b:=
  IsLocalization.Away.liftAlgHom (f:=toInfinityBase b) (FourRootAffineCoordinateRing318.coordinate b (some 0)) (by
    rw [toInfinityBase_z,s_zero,one_mul]
    exact IsUnit.of_mul_eq_one_right _ (u_ui b))
@[simp] lemma toAffine_map (a:Infinity b):toAffine b (algebraMap (Infinity b) (InfinityOverlap b) a)=toAffineBase b a:=by
  simp [toAffine,IsLocalization.Away.liftAlgHom_apply]
@[simp] lemma toInfinity_map (a:Affine b):toInfinity b (algebraMap (Affine b) (AffineOverlap b) a)=toInfinityBase b a:=by
  simp [toInfinity,IsLocalization.Away.liftAlgHom_apply]
@[simp] lemma toAffine_u:toAffine b (u b)=zi b:=by simp [u]
@[simp] lemma toAffine_s (k:Fin 4):toAffine b (s b k)=z b k*zi b:=by simp [s]
@[simp] lemma toInfinity_t:toInfinity b (t b)=algebraMap ℂ (InfinityOverlap b) (b 0)+ui b^2:=by simp [t]
@[simp] lemma toInfinity_z (k:Fin 4):toInfinity b (z b k)=s b k*ui b:=by simp [z]
@[simp] lemma toAffine_ui:toAffine b (ui b)=z b 0:=by
  have h:=congrArg (toAffine b) (u_ui b)
  simp only [map_mul,map_one,toAffine_u] at h
  calc
    _=(z b 0*zi b)*toAffine b (ui b):=by rw [z_zi,one_mul]
    _=z b 0*(zi b*toAffine b (ui b)):=by ring
    _=z b 0:=by rw [h,mul_one]
@[simp] lemma toInfinity_zi:toInfinity b (zi b)=u b:=by
  have h:=congrArg (toInfinity b) (z_zi b)
  simp only [map_mul,map_one,toInfinity_z,s_zero,one_mul] at h
  calc
    _=(u b*ui b)*toInfinity b (zi b):=by rw [u_ui,one_mul]
    _=u b*(ui b*toInfinity b (zi b)):=by ring
    _=u b:=by rw [h,mul_one]

lemma inverse_left:(toInfinity b).comp (toAffine b)=AlgHom.id ℂ (InfinityOverlap b):=by
  apply IsLocalization.algHom_ext (Submonoid.powers (FourRootInfinityCoordinateRing318.coordinate b none))
  apply FourRootInfinityCoordinateRing318.hom_ext
  intro k
  cases k with
  | none=>change toInfinity b (toAffine b (u b))=u b;simp
  | some k=>
    change toInfinity b (toAffine b (s b k))=s b k
    simp only [toAffine_s,map_mul,toInfinity_z,toInfinity_zi]
    calc
      (s b k*ui b)*u b=s b k*(u b*ui b):=by ring
      _=s b k:=by rw [u_ui,mul_one]
lemma inverse_right:(toAffine b).comp (toInfinity b)=AlgHom.id ℂ (AffineOverlap b):=by
  apply IsLocalization.algHom_ext (Submonoid.powers (FourRootAffineCoordinateRing318.coordinate b (some 0)))
  apply FourRootAffineCoordinateRing318.hom_ext
  intro k
  cases k with
  | none=>
    change toAffine b (toInfinity b (t b))=t b
    rw [toInfinity_t,map_add,map_pow,AlgHom.commutes,toAffine_ui,finite_relation]
    ring
  | some k=>
    change toAffine b (toInfinity b (z b k))=z b k
    simp only [toInfinity_z,map_mul,toAffine_s,toAffine_ui]
    calc
      (z b k*zi b)*z b 0=z b k*(z b 0*zi b):=by ring
      _=z b k:=by rw [z_zi,mul_one]

/-- Actual algebra isomorphism of the TWO specified principal-open
coordinate rings, retaining the full normalized infinity sign data. -/
@[expose] def overlapEquiv:InfinityOverlap b≃ₐ[ℂ]AffineOverlap b:=
  AlgEquiv.ofAlgHom (toAffine b) (toInfinity b) (inverse_right b) (inverse_left b)
end FourRootCoordinateOverlap318
