module
public import FifthBranchEquation318
public import FifthCharacterOrder318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace FifthBranchLocal318
open Polynomial QuadraticPresentation318 FifthCharacterShortPolynomial318 FifthBranchEquation318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev Quartic:=FifthCharacterOrder318.Order
@[expose] def denominator:Quartic:=algebraMap ℚ[X] Quartic branchFactor
abbrev Local:=Localization.Away denominator
@[expose] def polyMap:ℚ[X]→ₐ[ℚ]Local:=IsScalarTower.toAlgHom ℚ ℚ[X] Local
@[expose] def t:Local:=algebraMap ℚ[X] Local X
@[expose] def w:Local:=algebraMap Quartic Local (AdjoinRoot.root (polynomial FifthCharacterPolynomial318.quartic))
@[expose] def hUnit:Localˣ:=(IsLocalization.Away.algebraMap_isUnit (S:=Local) denominator).unit
@[expose] def nUnit:Localˣ:=Units.map (algebraMap ℚ Local).toMonoidHom yScale
@[simp] lemma poly_C (r:ℚ):polyMap (C r)=algebraMap ℚ Local r:=polyMap.commutes r
@[simp] lemma poly_X:polyMap X=t:=rfl
lemma hUnit_value:(hUnit:Local)=polyMap branchFactor:=by
  calc
    _=algebraMap Quartic Local denominator:=(IsLocalization.Away.algebraMap_isUnit (S:=Local) denominator).unit_spec
    _=polyMap branchFactor:=(IsScalarTower.algebraMap_apply ℚ[X] Quartic Local branchFactor).symm
lemma nUnit_value:(nUnit:Local)=algebraMap ℚ Local (yScale:ℚ):=rfl
lemma curve_equation:w^2=t*(hUnit:Local):=by
  have h:=congrArg (algebraMap Quartic Local) (root_square FifthCharacterPolynomial318.quartic)
  rw [map_pow,←IsScalarTower.algebraMap_apply] at h
  exact h.trans ((congrArg polyMap quartic_factor).trans (by
    rw [map_mul,poly_X,hUnit_value]))
lemma polynomial_equation:(nUnit:Local)^2*(hUnit:Local)=
    (algebraMap ℚ Local (xScale:ℚ)+algebraMap ℚ Local shift*t)^3+
      algebraMap ℚ Local A*(algebraMap ℚ Local (xScale:ℚ)+algebraMap ℚ Local shift*t)*t^2+
      algebraMap ℚ Local B*t^3:=by
  have h:=congrArg polyMap infinity_identity
  simpa only [map_mul,map_add,map_pow,poly_C,poly_X,←hUnit_value,←nUnit_value] using h
@[expose] def U:Local:=outU (algebraMap ℚ Local (xScale:ℚ)) (algebraMap ℚ Local shift) t w nUnit hUnit
@[expose] def V:Local:=outV t w nUnit hUnit
lemma equation:V-U^3-algebraMap ℚ Local A*U*V^2-algebraMap ℚ Local B*V^3=0:=
  regular_equation _ _ _ _ _ _ _ _ curve_equation polynomial_equation
/-- Actual regular infinity-chart map on the whole open D(h(t)),
which contains the original quartic branch point t=w=0. -/
@[expose] def infinityMap:InfinityChart318.Ring A B→ₐ[ℚ]Local:=InfinityChart318.lift A B U V equation
@[simp] lemma infinityMap_x:infinityMap (InfinityChart318.x A B)=U:=InfinityChart318.lift_x ..
@[simp] lemma infinityMap_z:infinityMap (InfinityChart318.z A B)=V:=InfinityChart318.lift_z ..
/-- The literal original quartic branch point, before localizing. -/
@[expose] def origin:Quartic→ₐ[ℚ]ℚ:=
  AdjoinRoot.liftAlgHom (polynomial FifthCharacterPolynomial318.quartic) (Polynomial.aeval (0:ℚ)) 0 (by
    simp [polynomial,FifthCharacterPolynomial318.quartic])
lemma origin_polynomial (p:ℚ[X]):origin (algebraMap ℚ[X] Quartic p)=p.eval 0:=by
  change origin (AdjoinRoot.of _ p)=_
  rw [origin,AdjoinRoot.liftAlgHom_of]
  simp
@[simp] lemma origin_root:origin (AdjoinRoot.root (polynomial FifthCharacterPolynomial318.quartic))=0:=
  AdjoinRoot.liftAlgHom_root _ _ _ _
lemma origin_denominator:origin denominator=branchFactor.eval 0:=origin_polynomial _
@[expose] def atOrigin:Local→ₐ[ℚ]ℚ:=
  IsLocalization.Away.liftAlgHom (f:=origin) denominator (by
    rw [origin_denominator]
    exact isUnit_iff_ne_zero.mpr branchFactor_zero)
@[simp] theorem atOrigin_on_quartic (r:Quartic):atOrigin (algebraMap Quartic Local r)=origin r:=by
  simp [atOrigin,IsLocalization.Away.liftAlgHom_apply]
@[simp] lemma atOrigin_w:atOrigin w=0:=by rw [w,atOrigin_on_quartic,origin_root]
@[simp] lemma atOrigin_U:atOrigin U=0:=by
  simp only [U,outU,map_mul,atOrigin_w,mul_zero,zero_mul]
@[simp] lemma atOrigin_V:atOrigin V=0:=by
  simp only [V,outV,map_mul,atOrigin_w,mul_zero,zero_mul]
/-- The actual branch map lands at the actual infinity origin. -/
theorem origin_composition:atOrigin.comp infinityMap=InfinityChart318.origin A B:=by
  apply InfinityChart318.hom_ext
  · simp only [AlgHom.comp_apply,infinityMap_x,atOrigin_U,InfinityChart318.origin_x]
  · simp only [AlgHom.comp_apply,infinityMap_z,atOrigin_V,InfinityChart318.origin_z]
end FifthBranchLocal318
