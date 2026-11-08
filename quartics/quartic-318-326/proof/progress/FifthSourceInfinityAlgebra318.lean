module
public import FifthSourceInfinityCoordinates318
public import WeierstrassOverlap318
public section
noncomputable section
namespace FifthSourceInfinityAlgebra318
open Polynomial QuadraticPresentation318 SourceTwistArithmetic318 FifthCharacterShortPolynomial318
open FifthSourceInfinityCoordinates318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField : Field L:=(KummerTensorField318.source_raw_field units).toField
lemma relation : y^2-x^3-algebraMap ℚ I A*x-algebraMap ℚ I B=0:=by
  apply InfinityOpenFractionField318.openEmbedding_injective units
  change embedding (y^2-x^3-algebraMap ℚ I A*x-algebraMap ℚ I B)=embedding 0
  simp only [map_sub,map_pow,map_mul,map_zero,RingHom.map_rat_algebraMap,x_embedding,y_embedding]
  have h:=congrArg rawMap (ShortAffineJacobian318.relation A B)
  simpa only [map_sub,map_pow,map_mul,map_zero,RingHom.map_rat_algebraMap] using h
/-- Whole actual contact infinity-order map into the finite fifth short chart. -/
@[expose] def shortMap:Short→ₐ[ℚ]I:=WeierstrassOverlap318.affineLift A B x y relation
@[simp] theorem shortMap_x:shortMap (ShortAffineJacobian318.x A B)=x:=WeierstrassOverlap318.affineLift_x ..
@[simp] theorem shortMap_y:shortMap (ShortAffineJacobian318.y A B)=y:=WeierstrassOverlap318.affineLift_y ..
/-- Equality of the actual entire coordinate maps inside the original full field. -/
theorem original_field_square : embedding.comp shortMap.toRingHom=rawMap:=by
  let f:Short→ₐ[ℚ]L:={ embedding.comp shortMap.toRingHom with commutes':=by intro q;exact RingHom.map_rat_algebraMap _ _ }
  let g:Short→ₐ[ℚ]L:={ rawMap with commutes':=by intro q;exact RingHom.map_rat_algebraMap _ _ }
  have h:f=g:=by
    apply WeierstrassOverlap318.affine_hom_ext
    · change embedding (shortMap (ShortAffineJacobian318.x A B))=rawMap _
      rw [shortMap_x,x_embedding]
    · change embedding (shortMap (ShortAffineJacobian318.y A B))=rawMap _
      rw [shortMap_y,y_embedding]
  exact congrArg AlgHom.toRingHom h
end FifthSourceInfinityAlgebra318
