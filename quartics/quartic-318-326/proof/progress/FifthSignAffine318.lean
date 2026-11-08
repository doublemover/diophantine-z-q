module
public import FifthSourceOverlap318
public import FifthSourceInfinityCoordinates318
public import SourceSignFieldComparison318
public import ChartNegation318
public section
noncomputable section
namespace FifthSignAffine318
open SourceTwistArithmetic318 ContactKummerOrder318 FifthCharacterShortPolynomial318
open FifthSourceInfinityCoordinates318
set_option maxHeartbeats 650000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
@[expose] def sign (b:Fin 4→Bool):RatFunc ℚ:=
  CharacterRoot318.sign (F:=RatFunc ℚ) FifthCharacterField318.support b
@[expose] def sigma (b:Fin 4→Bool):L≃ₐ[RatFunc ℚ]L:=
  FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b
lemma sign_cases (b:Fin 4→Bool):sign b=1 ∨ sign b=-1:=by
  apply sq_eq_one_iff.mp
  unfold sign CharacterRoot318.sign
  rw [←Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  cases h:b i <;> simp [h]
lemma sigma_rat (b:Fin 4→Bool) (q:ℚ):sigma b (algebraMap ℚ L q)=algebraMap ℚ L q:=
  (sigma b).toRingHom.map_rat_algebraMap q
lemma sigma_t (b:Fin 4→Bool):sigma b (InfinityFieldCoordinates318.t units)=InfinityFieldCoordinates318.t units:=
  (sigma b).commutes RatFunc.X
lemma sigma_x (b:Fin 4→Bool):sigma b (rawMap (ShortAffineJacobian318.x A B))=rawMap (ShortAffineJacobian318.x A B):=by
  rw [raw_x,map_add,map_mul,map_inv₀,sigma_t]
  rw [sigma_rat,sigma_rat]
lemma sigma_root (b:Fin 4→Bool):sigma b FifthCharacterField318.root=
    algebraMap (RatFunc ℚ) L (sign b)*FifthCharacterField318.root:=CharacterRoot318.sign_action _ _ _
lemma sigma_y_positive (b:Fin 4→Bool) (h:sign b=1):
    sigma b (rawMap (ShortAffineJacobian318.y A B))=rawMap (ShortAffineJacobian318.y A B):=by
  rw [raw_y,map_mul,map_mul,map_pow,map_inv₀,sigma_t,sigma_root,h,map_one,one_mul]
  rw [sigma_rat]
lemma sigma_y_negative (b:Fin 4→Bool) (h:sign b=-1):
    sigma b (rawMap (ShortAffineJacobian318.y A B))= -rawMap (ShortAffineJacobian318.y A B):=by
  rw [raw_y,map_mul,map_mul,map_pow,map_inv₀,sigma_t,sigma_root,h,map_neg,map_one,neg_one_mul]
  rw [sigma_rat]
  ring
lemma open_embedding (r:Short):SourceOpenFractionField318.openEmbedding units (FifthSourceOverlap318.shortMap r)=rawMap r:=
  FifthSourceOverlap318.shortMap_raw r
/-- The entire actual unbranched-source coordinate map is fixed exactly for positive full-character sign. -/
theorem positive (b:Fin 4→Bool) (h:sign b=1):
    ((ContactGlobalSigns318.openEquiv units b).toAlgHom.restrictScalars ℚ).comp FifthSourceOverlap318.shortMap=
      FifthSourceOverlap318.shortMap:=by
  apply WeierstrassOverlap318.affine_hom_ext
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (FifthSourceOverlap318.shortMap _))=_
    rw [SourceSignFieldComparison318.open_embedding,open_embedding]
    exact sigma_x b
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (FifthSourceOverlap318.shortMap _))=_
    rw [SourceSignFieldComparison318.open_embedding,open_embedding]
    exact sigma_y_positive b h
/-- Negative full-character sign is the actual affine elliptic negation. -/
theorem negative (b:Fin 4→Bool) (h:sign b=-1):
    ((ContactGlobalSigns318.openEquiv units b).toAlgHom.restrictScalars ℚ).comp FifthSourceOverlap318.shortMap=
      FifthSourceOverlap318.shortMap.comp (ChartNegation318.affineNeg A B):=by
  apply WeierstrassOverlap318.affine_hom_ext
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (FifthSourceOverlap318.shortMap _))=
      SourceOpenFractionField318.openEmbedding units (FifthSourceOverlap318.shortMap (ChartNegation318.affineNeg A B _))
    rw [ChartNegation318.affineNeg_x,SourceSignFieldComparison318.open_embedding,open_embedding]
    exact sigma_x b
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (FifthSourceOverlap318.shortMap _))=
      SourceOpenFractionField318.openEmbedding units (FifthSourceOverlap318.shortMap (ChartNegation318.affineNeg A B _))
    rw [ChartNegation318.affineNeg_y,map_neg,map_neg,SourceSignFieldComparison318.open_embedding,open_embedding]
    exact sigma_y_negative b h
end FifthSignAffine318
