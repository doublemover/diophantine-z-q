module
public import ThreeTorsionTangentUniversal318
public section
noncomputable section
namespace TangentDiagonalNatural318
open TangentOpenAlgebra318 TangentDiagonal318
open RelativeChordAlgebra318 (PairRing)
open scoped TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S V:Type*} [CommRing R] [CommRing S] [CommRing V] [Algebra R S] [Algebra R V]
  (A B:R) (φ:ShortAffineJacobian318.Ring A B→ₐ[R]S) (h:S→ₐ[R]V)
local instance pairCommRing : CommRing (PairRing A B):=inferInstance
local instance pairAlgebra : Algebra R (PairRing A B):=inferInstance

lemma pair_natural (z:PairRing A B) : h (pair A B φ z)=pair A B (h.comp φ) z:=by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp only [pair,Algebra.TensorProduct.lift_tmul,map_mul,AlgHom.comp_apply]
  | add a b ha hb => simp only [map_add,ha,hb]

lemma diagonal_comp_base (hu:IsUnit (2*φ (ShortAffineJacobian318.y A B))) :
    (diagonal A B φ hu).toRingHom.comp
      (algebraMap (PairRing A B) (TangentRing A B))=(pair A B φ).toRingHom:=by
  have hp:IsUnit (pair A B φ (ordinateSum A B)):=by
    simpa only [ordinateSum,map_add,pair_left,pair_right,two_mul] using hu
  exact IsLocalization.Away.lift_comp (S:=TangentRing A B) (g:=(pair A B φ).toRingHom)
    (ordinateSum A B) hp

lemma natural (hu:IsUnit (2*φ (ShortAffineJacobian318.y A B)))
    (hv:IsUnit (2*(h.comp φ) (ShortAffineJacobian318.y A B))) :
    h.comp (diagonal A B φ hu)=diagonal A B (h.comp φ) hv:=by
  apply IsLocalization.algHom_ext (Submonoid.powers (ordinateSum A B))
  apply AlgHom.ext
  intro z
  simp only [AlgHom.comp_apply,Algebra.algHom,IsScalarTower.toAlgHom_apply,diagonal,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
  exact pair_natural A B φ h z

end TangentDiagonalNatural318
