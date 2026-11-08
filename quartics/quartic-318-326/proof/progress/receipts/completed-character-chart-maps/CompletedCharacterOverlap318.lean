module
public import CompletedCharacterInfinity318
public import WeierstrassOverlap318
public section
noncomputable section
namespace CompletedCharacterOverlap318
open Polynomial SourceTwistArithmetic318 CompletedCharacterInfinity318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev O:=ContactKummerOrder318.OpenOrder units
local instance rawField : Field L:=(KummerTensorField318.source_raw_field units).toField

@[expose] def sourceRestriction : SourceCharacterAlgebra318.Source→ₐ[ℚ]O where
  __ := SourceOpenFractionField318.orderToOpen units
  commutes' := RingHom.map_rat_algebraMap _
@[expose] def finiteMap (i:Fin 4):Published i→ₐ[ℚ]O:=
  sourceRestriction.comp (SourceCharacterAlgebra318.publishedToSource i)
@[expose] def infinityMap (i:Fin 4):InfinityChart318.Ring (publishedA i) (publishedB i)→ₐ[ℚ]O:=
  (ContactOverlapAlgebraMaps318.infinityMap units).comp (CompletedCharacterInfinity318.infinityMap i)

lemma finiteMap_embedding (i:Fin 4) (a:Published i):
    SourceOpenFractionField318.openEmbedding units (finiteMap i a)=rawMap i a:=
  SourceOpenFractionField318.openEmbedding_on_order units _

lemma infinityMap_x_embedding (i:Fin 4):SourceOpenFractionField318.openEmbedding units
    (infinityMap i (InfinityChart318.x (publishedA i) (publishedB i)))=rawX i/rawY i:=by
  change SourceOpenFractionField318.openEmbedding units
    (InfinityOverlapLocalization318.toOpen units (CompletedCharacterInfinity318.infinityMap i _))=_
  rw [InfinityOverlapLocalization318.toOpen_embedding,CompletedCharacterInfinity318.infinityMap_x,
    CompletedCharacterInfinity318.x_embedding]

lemma infinityMap_z_embedding (i:Fin 4):SourceOpenFractionField318.openEmbedding units
    (infinityMap i (InfinityChart318.z (publishedA i) (publishedB i)))=(rawY i)⁻¹:=by
  change SourceOpenFractionField318.openEmbedding units
    (InfinityOverlapLocalization318.toOpen units (CompletedCharacterInfinity318.infinityMap i _))=_
  rw [InfinityOverlapLocalization318.toOpen_embedding,CompletedCharacterInfinity318.infinityMap_z,
    CompletedCharacterInfinity318.z_embedding]

/-- The actual y-coordinate is invertible on the whole source overlap,
with the specified regular infinity z-coordinate as its inverse. -/
lemma finite_y_inverse (i:Fin 4):
    finiteMap i (ShortAffineJacobian318.y (publishedA i) (publishedB i))*
      infinityMap i (InfinityChart318.z (publishedA i) (publishedB i))=1:=by
  apply SourceOpenFractionField318.openEmbedding_injective units
  rw [map_mul,finiteMap_embedding,infinityMap_z_embedding,map_one]
  exact mul_inv_cancel₀ (rawY_ne_zero i)

lemma finite_y_unit (i:Fin 4):
    IsUnit (finiteMap i (ShortAffineJacobian318.y (publishedA i) (publishedB i))):=
  isUnit_iff_exists_inv.mpr ⟨_,finite_y_inverse i⟩

/-- An actual map into the full finite/infinity overlap of the target
completed elliptic curve, with the existing finite-map restriction. -/
@[expose] def overlapMap (i:Fin 4):
    WeierstrassOverlap318.AffineOverlap (publishedA i) (publishedB i)→ₐ[ℚ]O:=
  IsLocalization.Away.liftAlgHom (f:=finiteMap i)
    (ShortAffineJacobian318.y (publishedA i) (publishedB i)) (finite_y_unit i)

@[simp] lemma overlapMap_on_finite (i:Fin 4) (a:Published i):
    overlapMap i (algebraMap (Published i) _ a)=finiteMap i a:=
  by simp [overlapMap,IsLocalization.Away.liftAlgHom_apply]

lemma inverse_embedding (i:Fin 4):SourceOpenFractionField318.openEmbedding units
    (overlapMap i (WeierstrassOverlap318.ai (publishedA i) (publishedB i)))=(rawY i)⁻¹:=by
  have h:=congrArg (fun a=>SourceOpenFractionField318.openEmbedding units (overlapMap i a))
    (WeierstrassOverlap318.ay_ai (publishedA i) (publishedB i))
  simp only [map_mul,map_one,WeierstrassOverlap318.ay,overlapMap_on_finite,finiteMap_embedding] at h
  apply mul_left_cancel₀ (rawY_ne_zero i)
  rw [mul_inv_cancel₀ (rawY_ne_zero i)]
  exact h

/-- Exact equality of the two coordinate algebra maps on the entire
actual common open, not just agreement of their abstract fraction fields. -/
theorem infinity_compatibility (i:Fin 4):
    (overlapMap i).comp (WeierstrassOverlap318.toAffineBase (publishedA i) (publishedB i))=
      infinityMap i:=by
  apply InfinityChart318.hom_ext
  · apply SourceOpenFractionField318.openEmbedding_injective units
    simp only [AlgHom.comp_apply,WeierstrassOverlap318.toAffineBase_x,map_mul,
      WeierstrassOverlap318.ax,overlapMap_on_finite,finiteMap_embedding,inverse_embedding,
      infinityMap_x_embedding]
    rfl
  · apply SourceOpenFractionField318.openEmbedding_injective units
    simp only [AlgHom.comp_apply,WeierstrassOverlap318.toAffineBase_z,inverse_embedding,
      infinityMap_z_embedding]
end CompletedCharacterOverlap318
