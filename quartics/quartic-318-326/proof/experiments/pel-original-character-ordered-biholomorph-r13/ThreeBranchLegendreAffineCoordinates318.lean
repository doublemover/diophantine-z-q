module
public import ThreeBranchLegendreAffineIso318
public import ThreeBranchLegendreInfinityAlgebra318
public section
noncomputable section
namespace ThreeBranchLegendreAffineCoordinates318
open Polynomial QuadraticPresentation318 ThreeBranchLegendrePolynomial318
open ThreeBranchLegendreAffineIso318
set_option maxHeartbeats 800000
variable (a b c:ℂ) (hab:b≠a)
abbrev A:=NormalizedLegendreProjectiveModel318.A (parameter a b c)
abbrev B:=NormalizedLegendreProjectiveModel318.B (parameter a b c)
abbrev Target:=ShortAffineJacobian318.Ring (A a b c) (B a b c)
@[expose] def t:Cubic a b c:=algebraMap ℂ[X] _ X
@[expose] def v:Cubic a b c:=AdjoinRoot.root (polynomial (cubic a b c))

lemma standard_polynomial (p:ℂ[X]):
    standardEquiv a b c (algebraMap ℂ[X] (Short a b c) p)=
      algebraMap ℂ[X] (AffineCoordinateDomain318.CoordinateRing (A a b c) (B a b c)) p:=by
  simp only [standardEquiv,AdjoinRoot.algebraMap_eq,AdjoinRoot.coe_algEquivOfEq,
    AdjoinRoot.coe_algHomOfDvd,AdjoinRoot.liftAlgHom_of]
  rfl

lemma standard_root:
    standardEquiv a b c (AdjoinRoot.root (polynomial (shortPolynomial a b c)))=
      AffineCoordinateDomain318.y (A a b c) (B a b c):=by
  simp only [standardEquiv,AdjoinRoot.algEquivOfEq_root,AffineCoordinateDomain318.y]

/-- The genuine old equivalence, not a newly selected coordinate change,
sends the original cubic coordinate to d*x+center. -/
lemma coordinate_t:coordinateEquiv a b c hab (t a b c)=
    algebraMap ℂ (Target a b c) (b-a)*ShortAffineJacobian318.x (A a b c) (B a b c)+
      algebraMap ℂ (Target a b c) (ThreeBranchLegendreInfinityAlgebra318.center a b c):=by
  unfold coordinateEquiv
  rw [AlgEquiv.trans_apply,AlgEquiv.trans_apply,t,rootEquiv_polynomial,standard_polynomial]
  rw [baseChange_apply]
  simp only [Polynomial.X_comp,map_add,map_mul]
  change AffineCoordinateDomain318.backward (A a b c) (B a b c)
    (algebraMap ℂ _ (b-a)*AffineCoordinateDomain318.x (A a b c) (B a b c)+
      algebraMap ℂ _ (ThreeBranchLegendreInfinityAlgebra318.center a b c))=_
  rw [map_add,map_mul,AlgHom.commutes,AlgHom.commutes,AffineCoordinateDomain318.backward_x]

lemma coordinate_v:coordinateEquiv a b c hab (v a b c)=
    algebraMap ℂ (Target a b c) (rootScale a b)*
      ShortAffineJacobian318.y (A a b c) (B a b c):=by
  unfold coordinateEquiv
  rw [AlgEquiv.trans_apply,AlgEquiv.trans_apply,v,rootEquiv_root,map_mul,
    standard_polynomial,standard_root]
  change AffineCoordinateDomain318.backward (A a b c) (B a b c)
    (algebraMap ℂ _ (rootScale a b)*AffineCoordinateDomain318.y (A a b c) (B a b c))=_
  rw [map_mul,AlgHom.commutes,AffineCoordinateDomain318.backward_y]

/-- Exact inverse coordinate formulas in the whole cubic ring. No
function-field restriction and no nonvanishing of a source coordinate. -/
lemma inverse_x:(coordinateEquiv a b c hab).symm
    (ShortAffineJacobian318.x (A a b c) (B a b c))=
      algebraMap ℂ (Cubic a b c) (b-a)⁻¹*
        (t a b c-algebraMap ℂ (Cubic a b c)
          (ThreeBranchLegendreInfinityAlgebra318.center a b c)):=by
  apply (coordinateEquiv a b c hab).injective
  rw [AlgEquiv.apply_symm_apply,map_mul,map_sub,AlgEquiv.commutes,AlgEquiv.commutes,coordinate_t]
  have h:algebraMap ℂ (Target a b c) (b-a)⁻¹*algebraMap ℂ (Target a b c) (b-a)=1:=by
    rw [←map_mul,inv_mul_cancel₀ (sub_ne_zero.mpr hab),map_one]
  calc
    _=(algebraMap ℂ (Target a b c) (b-a)⁻¹*algebraMap ℂ (Target a b c) (b-a))*
      ShortAffineJacobian318.x (A a b c) (B a b c):=by rw [h,one_mul]
    _=_:=by ring

lemma inverse_y:(coordinateEquiv a b c hab).symm
    (ShortAffineJacobian318.y (A a b c) (B a b c))=
      algebraMap ℂ (Cubic a b c) (rootScale a b)⁻¹*v a b c:=by
  apply (coordinateEquiv a b c hab).injective
  rw [AlgEquiv.apply_symm_apply,map_mul,AlgEquiv.commutes,coordinate_v]
  rw [←mul_assoc,←map_mul,inv_mul_cancel₀ (rootScale_ne_zero a b hab),map_one,one_mul]
end ThreeBranchLegendreAffineCoordinates318
