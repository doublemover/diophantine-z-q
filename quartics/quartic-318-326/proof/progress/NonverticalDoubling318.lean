module
public import TangentDiagonalNatural318
public import ThreeTorsionTangentScheme318
public section
noncomputable section
namespace NonverticalDoubling318
open ThreeTorsionScheme318 ThreeTorsionAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R)
abbrev Curve:=ShortAffineJacobian318.Ring A B
@[expose] def denominator : Curve A B:=2*ShortAffineJacobian318.y A B
abbrev OpenRing:=Localization.Away (denominator A B)
@[expose] def curveMap : Curve A B→ₐ[R]OpenRing A B:=IsScalarTower.toAlgHom R _ _

lemma unit : IsUnit (2*curveMap A B (ShortAffineJacobian318.y A B)):=by
  simpa only [denominator,map_mul,map_ofNat,curveMap,IsScalarTower.toAlgHom_apply]
    using IsLocalization.Away.algebraMap_isUnit (S:=OpenRing A B) (denominator A B)

@[expose] def double : Curve A B→ₐ[R]OpenRing A B:=
  (TangentDiagonal318.diagonal A B (curveMap A B) (unit A B)).comp (TangentOpenAlgebra318.tangentMap A B)
@[expose] def negative : Curve A B→ₐ[R]OpenRing A B:=
  (curveMap A B).comp (ChartNegation318.affineNeg A B)

variable [Invertible (3:R)] (hD:IsUnit (-16*(4*A^3+27*B^2)))
@[expose] def toTorsion : OpenRing A B→ₐ[R]Ring A B hD:=
  IsLocalization.Away.liftAlgHom (f:=coordinateMap A B hD) (denominator A B) (by
    simpa only [denominator,map_mul,map_ofNat] using ThreeTorsionTangentScheme318.ordinate_unit A B hD)

lemma toTorsion_curveMap : (toTorsion A B hD).comp (curveMap A B)=coordinateMap A B hD:=by
  apply AlgHom.ext
  intro z
  simp only [AlgHom.comp_apply,curveMap,IsScalarTower.toAlgHom_apply,toTorsion,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]

lemma condition : (toTorsion A B hD).comp (double A B)=
    (toTorsion A B hD).comp (negative A B):=by
  have hu:IsUnit (2*((toTorsion A B hD).comp (curveMap A B)) (ShortAffineJacobian318.y A B)):=by
    rw [toTorsion_curveMap]
    exact ThreeTorsionTangentScheme318.ordinate_unit A B hD
  have hn:=TangentDiagonalNatural318.natural A B (curveMap A B) (toTorsion A B hD) (unit A B) hu
  simp only [toTorsion_curveMap] at hn
  unfold double negative
  rw [←AlgHom.comp_assoc,hn,←AlgHom.comp_assoc]
  simpa only [toTorsion_curveMap,ThreeTorsionTangentScheme318.diagonalMap] using
    ThreeTorsionTangentScheme318.double_neg_coordinates A B hD

end NonverticalDoubling318
