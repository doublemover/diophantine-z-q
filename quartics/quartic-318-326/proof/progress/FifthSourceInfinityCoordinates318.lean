module
public import InfinityCharacterUnits318
public import CompletedCharacterInfinity318
public import FifthShortFraction318
public section
noncomputable section
namespace FifthSourceInfinityCoordinates318
open Polynomial QuadraticPresentation318 SourceTwistArithmetic318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev I:=InfinityOpenChart318.OpenOrder units
abbrev L:=InfinityFieldCoordinates318.L units
abbrev Short:=ShortAffineJacobian318.Ring A B
local instance rawField : Field L:=(KummerTensorField318.source_raw_field units).toField
@[expose] def embedding:I→+*L:=InfinityOpenFractionField318.openEmbedding units
@[expose] def fieldInclusion:FifthCharacterField318.field→+*L:=FifthCharacterField318.field.subtype
@[expose] def rawMap:Short→+*L:=fieldInclusion.comp FifthShortFraction318.embedding
@[expose] def u:I:=algebraMap ℚ I ((units 0)⁻¹:ℚˣ)*CompletedCharacterInfinity318.u^2
@[expose] def v:I:=algebraMap ℚ I (units 0:ℚ)^2*∏i:Fin 4,InfinityCharacterUnits318.indexedRatio units i

lemma u_embedding : embedding u=(InfinityFieldCoordinates318.t units)⁻¹:=by
  simp only [u,map_mul,map_pow,RingHom.map_rat_algebraMap,embedding,
    CompletedCharacterInfinity318.u_embedding]
  exact (InfinityFieldCoordinates318.reciprocal_contact_square units).symm

lemma ratio_product_embedding : embedding (∏i:Fin 4,InfinityCharacterUnits318.indexedRatio units i)=
    FifthCharacterField318.root/(InfinityFieldCoordinates318.root units 0)^4:=by
  simp only [embedding,map_prod,InfinityCharacterUnits318.indexedRatio_embedding,
    Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rfl
lemma v_embedding : embedding v=(InfinityFieldCoordinates318.t units)⁻¹^2*FifthCharacterField318.root:=by
  rw [v,map_mul,map_pow,RingHom.map_rat_algebraMap,ratio_product_embedding]
  have h:(InfinityFieldCoordinates318.root units 0)^4=
      (algebraMap ℚ L (units 0:ℚ))^2*(InfinityFieldCoordinates318.t units)^2:=by
    calc
      _=((InfinityFieldCoordinates318.root units 0)^2)^2:=by ring
      _=_:=by rw [InfinityFieldCoordinates318.root_zero_square];simp only [InfinityFieldCoordinates318.constant,mul_pow]
  rw [h]
  have hc:algebraMap ℚ L (units 0:ℚ)≠0:=InfinityFieldCoordinates318.constant_ne_zero units (units 0).ne_zero
  field_simp [InfinityFieldCoordinates318.t_ne_zero units,hc]

lemma original_t : (FifthReciprocalFieldCoordinates318.t:L)=InfinityFieldCoordinates318.t units:=by
  change (FifthCharacterOrder318.embedding (algebraMap ℚ[X] _ X):L)=_
  rw [FifthCharacterOrder318.embedding_on_polynomial]
  simp only [RatFunc.algebraMap_X]
  rfl
lemma original_y : (FifthReciprocalFieldCoordinates318.y:L)=FifthCharacterField318.root:=
  FifthReciprocalFieldCoordinates318.original_root
lemma subtype_rat (q:ℚ) :
    fieldInclusion (@algebraMap ℚ FifthShortFraction318.Field _ _ DivisionRing.toRatAlgebra q)=algebraMap ℚ L q:=by
  letI:Algebra ℚ FifthShortFraction318.Field:=DivisionRing.toRatAlgebra
  exact RingHom.map_rat_algebraMap fieldInclusion q
lemma subtype_inverse : fieldInclusion FifthReciprocalFieldCoordinates318.t⁻¹=
    (InfinityFieldCoordinates318.t units)⁻¹:=by
  exact (map_inv₀ fieldInclusion FifthReciprocalFieldCoordinates318.t).trans
    (congrArg Inv.inv original_t)
lemma raw_x : rawMap (ShortAffineJacobian318.x A B)=
    algebraMap ℚ L (xScale:ℚ)*(InfinityFieldCoordinates318.t units)⁻¹+algebraMap ℚ L shift:=by
  change fieldInclusion (FifthShortFraction318.embedding (ShortAffineJacobian318.x A B))=_
  rw [FifthShortFraction318.embedding_x]
  simp only [map_add,map_mul,subtype_inverse,subtype_rat]
lemma raw_y : rawMap (ShortAffineJacobian318.y A B)=
    algebraMap ℚ L (yScale:ℚ)*((InfinityFieldCoordinates318.t units)⁻¹^2*FifthCharacterField318.root):=by
  change fieldInclusion (FifthShortFraction318.embedding (ShortAffineJacobian318.y A B))=_
  rw [FifthShortFraction318.embedding_y]
  simp only [map_mul,map_pow,subtype_inverse,subtype_rat]
  rw [show fieldInclusion FifthReciprocalFieldCoordinates318.y=FifthCharacterField318.root from original_y]
@[expose] def x:I:=algebraMap ℚ I (xScale:ℚ)*u+algebraMap ℚ I shift
@[expose] def y:I:=algebraMap ℚ I (yScale:ℚ)*v
lemma x_embedding : embedding x=rawMap (ShortAffineJacobian318.x A B):=by
  rw [x,map_add,map_mul,RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap,u_embedding,raw_x]
lemma y_embedding : embedding y=rawMap (ShortAffineJacobian318.y A B):=by
  rw [y,map_mul,RingHom.map_rat_algebraMap,v_embedding,raw_y]
end FifthSourceInfinityCoordinates318
