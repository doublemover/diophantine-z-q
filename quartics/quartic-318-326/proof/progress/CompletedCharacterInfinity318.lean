module
public import InfinityCharacterUnits318
public import CubicInverseCoordinates318
public import InfinityChart318
public section
noncomputable section
namespace CompletedCharacterInfinity318
open Polynomial QuadraticPresentation318 SourceTwistArithmetic318 CubicWeierstrassPolynomial318
open CubicInverseCoordinates318
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev I:=InfinityOpenChart318.OpenOrder units
abbrev L:=InfinityFieldCoordinates318.L units
abbrev Published (i:Fin 4):=ShortAffineJacobian318.Ring (publishedA i) (publishedB i)
local instance rawField : Field L:=(KummerTensorField318.source_raw_field units).toField

@[expose] def rawMap (i:Fin 4):Published i→+*L:=
  (ContactKummerOrder318.embedding units).comp (SourceCharacterAlgebra318.publishedToSource i).toRingHom
@[expose] def rawX (i:Fin 4):L:=rawMap i (ShortAffineJacobian318.x (publishedA i) (publishedB i))
@[expose] def rawY (i:Fin 4):L:=rawMap i (ShortAffineJacobian318.y (publishedA i) (publishedB i))

lemma rawX_formula (i:Fin 4):rawX i=algebraMap ℚ L (xScale i:ℚ)*
    (InfinityFieldCoordinates318.t units-algebraMap ℚ L (centroid i)):=by
  change ContactKummerOrder318.embedding units (SourceCharacterAlgebra318.publishedToSource i _)=_
  rw [source_x,map_mul,map_sub,RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap,
    SourceFractionField318.embedding_on_polynomial,RatFunc.algebraMap_X]
  rfl

lemma rawY_formula (i:Fin 4):rawY i=algebraMap ℚ L (yScale i:ℚ)*
    CharacterRoot318.root (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i):=by
  change ContactKummerOrder318.embedding units (SourceCharacterAlgebra318.publishedToSource i _)=_
  rw [source_y,map_mul,RingHom.map_rat_algebraMap,SourceCharacterAlgebra318.toSource_embedding]
  exact congrArg (fun x:L=>algebraMap ℚ L (yScale i:ℚ)*x) (CubicCharacterFraction318.embedding_root i)

lemma rawY_ne_zero (i:Fin 4):rawY i≠0:=by
  rw [rawY_formula]
  exact mul_ne_zero (by simpa only [map_zero] using (algebraMap ℚ L).injective.ne (yScale i).ne_zero)
    (CharacterRoot318.root_ne_zero _ _)

lemma raw_relation (i:Fin 4):
    rawY i^2-rawX i^3-algebraMap ℚ L (publishedA i)*rawX i-algebraMap ℚ L (publishedB i)=0:=by
  have h:=congrArg (rawMap i) (ShortAffineJacobian318.relation (publishedA i) (publishedB i))
  simpa only [map_sub,map_mul,map_pow,map_zero,RingHom.map_rat_algebraMap,rawX,rawY] using h

@[expose] def coefficientUnit (i:Fin 4):Iˣ:=
  Units.map (algebraMap ℚ I).toMonoidHom (yScale i*(units 0)^3)*
    (InfinityCharacterUnits318.ratioProduct_unit units i).unit

lemma coefficientUnit_embedding (i:Fin 4):
    InfinityOpenFractionField318.openEmbedding units (coefficientUnit i:I)=
      (InfinityFieldCoordinates318.u units)^3*rawY i:=by
  change InfinityOpenFractionField318.openEmbedding units
    (algebraMap ℚ I (↑(yScale i*(units 0)^3):ℚ)*
      ↑(InfinityCharacterUnits318.ratioProduct_unit units i).unit)=_
  rw [map_mul,RingHom.map_rat_algebraMap,
    (InfinityCharacterUnits318.ratioProduct_unit units i).unit_spec]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,map_mul,map_pow]
  rw [rawY_formula]
  have h:=InfinityCharacterUnits318.character_normalization units i
  linear_combination algebraMap ℚ L (yScale i:ℚ)*h.symm

@[expose] def u:I:=ContactFrameNormalization318.infinityCoordinate units
lemma u_embedding : InfinityOpenFractionField318.openEmbedding units u=InfinityFieldCoordinates318.u units:=by
  simpa only [u,ContactFrameNormalization318.infinityCoordinate,Polynomial.aeval_X] using
    ReciprocalInfinityNormalization318.openEmbedding_on_polynomial units X

/-- Actual regular X/Y coordinate on the full source infinity neighborhood. -/
@[expose] def x (i:Fin 4):I:=algebraMap ℚ I (xScale i:ℚ)*u*
  (algebraMap ℚ I (units 0:ℚ)-algebraMap ℚ I (centroid i)*u^2)*(↑(coefficientUnit i)⁻¹:I)
/-- Actual regular Z/Y coordinate, including all points over infinity. -/
@[expose] def z (i:Fin 4):I:=u^3*(↑(coefficientUnit i)⁻¹:I)

lemma x_embedding (i:Fin 4):InfinityOpenFractionField318.openEmbedding units (x i)=rawX i/rawY i:=by
  simp only [x,map_mul,map_sub,map_pow,RingHom.map_rat_algebraMap,map_units_inv,
    coefficientUnit_embedding,u_embedding]
  rw [rawX_formula,InfinityFieldCoordinates318.recover_t units]
  simp only [InfinityFieldCoordinates318.constant]
  field_simp [InfinityFieldCoordinates318.u_ne_zero units,rawY_ne_zero i]

lemma z_embedding (i:Fin 4):InfinityOpenFractionField318.openEmbedding units (z i)=(rawY i)⁻¹:=by
  simp only [z,map_mul,map_pow,map_units_inv,coefficientUnit_embedding,u_embedding]
  field_simp [InfinityFieldCoordinates318.u_ne_zero units,rawY_ne_zero i]

/-- The literal completed Weierstrass infinity equation holds on the entire
actual contact infinity order, proved through its specified injective embedding. -/
theorem relation (i:Fin 4):z i-x i^3-algebraMap ℚ I (publishedA i)*x i*z i^2-
    algebraMap ℚ I (publishedB i)*z i^3=0:=by
  apply InfinityOpenFractionField318.openEmbedding_injective units
  simp only [map_sub,map_mul,map_pow,map_zero,RingHom.map_rat_algebraMap,x_embedding,z_embedding]
  field_simp [rawY_ne_zero i]
  linear_combination raw_relation i

/-- An actual Q-algebra map from the literal completed elliptic Y=1 chart,
not merely a rational map or equality of function fields. -/
@[expose] def infinityMap (i:Fin 4):InfinityChart318.Ring (publishedA i) (publishedB i)→ₐ[ℚ]I:=
  InfinityChart318.lift (publishedA i) (publishedB i) (x i) (z i) (relation i)

theorem infinityMap_x (i:Fin 4):infinityMap i (InfinityChart318.x (publishedA i) (publishedB i))=x i:=
  InfinityChart318.lift_x ..
theorem infinityMap_z (i:Fin 4):infinityMap i (InfinityChart318.z (publishedA i) (publishedB i))=z i:=
  InfinityChart318.lift_z ..
end CompletedCharacterInfinity318
