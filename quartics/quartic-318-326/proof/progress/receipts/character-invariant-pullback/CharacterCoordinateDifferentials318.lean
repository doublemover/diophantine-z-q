module
public import CubicInverseCoordinates318
public import AlgHomDifferential318
public section
noncomputable section
namespace CharacterCoordinateDifferentials318
open AlgebraicGeometry CategoryTheory Polynomial KaehlerDifferential
open SourceTwistArithmetic318 CubicInverseCoordinates318 CubicWeierstrassPolynomial318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev S := SourceCharacterAlgebra318.Source
@[expose] def t : S := algebraMap ℚ[X] S X
@[expose] def z (i:Fin 4) : S :=
  SourceCharacterAlgebra318.toSource i
    (AdjoinRoot.root (QuadraticPresentation318.polynomial (CubicWeierstrassPolynomial318.radicand i)))

/-- The actual finite coordinate algebra map has exactly this differential,
including the full scalar and centroid cancellation on the entire source ring. -/
theorem map_dx (i:Fin 4) :
    AlgHomDifferential318.map (SourceCharacterAlgebra318.publishedToSource i)
      (D ℚ (ShortAffineJacobian318.Ring (publishedA i) (publishedB i))
        (ShortAffineJacobian318.x (publishedA i) (publishedB i))) =
      algebraMap ℚ S (xScale i:ℚ) • D ℚ S t := by
  rw [AlgHomDifferential318.map_D,source_x,Derivation.leibniz,map_sub,
    Derivation.map_algebraMap,Derivation.map_algebraMap,smul_zero,add_zero,sub_zero]
  rfl

theorem map_dy (i:Fin 4) :
    AlgHomDifferential318.map (SourceCharacterAlgebra318.publishedToSource i)
      (D ℚ (ShortAffineJacobian318.Ring (publishedA i) (publishedB i))
        (ShortAffineJacobian318.y (publishedA i) (publishedB i))) =
      algebraMap ℚ S (yScale i:ℚ) • D ℚ S (z i) := by
  rw [AlgHomDifferential318.map_D,source_y,Derivation.leibniz,
    Derivation.map_algebraMap,smul_zero,add_zero]
  rfl

/-- Exact ratio of the coordinate scales: xScale/yScale is the published
coordinateScale, not its inverse. This fixes the pullback normalization. -/
theorem scales (i:Fin 4) :
    xScale i = CharacterPublishedModels318.scaleUnit i * yScale i := by
  unfold xScale yScale
  apply Units.ext
  simp only [Units.val_mul,Units.val_pow_eq_pow_val]
  have h:(↑(CharacterPublishedModels318.scaleUnit i):ℚ)*
      (↑((CharacterPublishedModels318.scaleUnit i)⁻¹):ℚ)=1:=Units.mul_inv _
  calc
    _ = (↑(twistUnit i):ℚ) *
      ((↑((CharacterPublishedModels318.scaleUnit i)⁻¹):ℚ)^2) *
      ((↑(CharacterPublishedModels318.scaleUnit i):ℚ)*
        (↑((CharacterPublishedModels318.scaleUnit i)⁻¹):ℚ)) := by rw [h,mul_one]
    _ = _ := by ring
end CharacterCoordinateDifferentials318
