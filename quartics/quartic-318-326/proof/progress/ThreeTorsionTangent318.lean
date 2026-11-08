module
public import TangentDiagonal318
public import ThreeTorsionTangentCriterion318
public import ThreeTorsionScheme318
public section
noncomputable section
namespace ThreeTorsionTangent318
open Polynomial TangentOpenAlgebra318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S] (A B:R)
  [Invertible (3:R)] (φ:ShortAffineJacobian318.Ring A B→ₐ[R]S)
  (hu:IsUnit (2*φ (ShortAffineJacobian318.y A B)))

/-- On the actual tangent diagonal, the normalized third-division equation
is exactly equality of the doubling morphism and actual affine negation. -/
theorem factor_iff_double_neg :
    (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R S)
      (φ (ShortAffineJacobian318.x A B))=0 ↔
    (TangentDiagonal318.diagonal A B φ hu).comp (tangentMap A B)=
      φ.comp (ChartNegation318.affineNeg A B) := by
  rw [ThreeTorsionTangentCriterion318.normalized_criterion A B _ _
    (TangentDiagonal318.diagonal A B φ hu (slope A B))
    (TangentDiagonal318.curve_relation A B φ)
    (TangentDiagonal318.slope_relation A B φ hu) hu]
  constructor
  · rintro ⟨hx,hy⟩
    apply WeierstrassOverlap318.affine_hom_ext
    · simpa only [AlgHom.comp_apply,tangentMap_x,ChartNegation318.affineNeg_x,
        x3,map_sub,map_pow,x1,x2,TangentDiagonal318.diagonal_left,
        TangentDiagonal318.diagonal_right] using hx
    · simpa only [AlgHom.comp_apply,tangentMap_y,ChartNegation318.affineNeg_y,
        y3,x3,map_sub,map_mul,map_pow,map_neg,x1,x2,y1,TangentDiagonal318.diagonal_left,
        TangentDiagonal318.diagonal_right] using hy
  · intro hh
    constructor
    · have hx:=AlgHom.congr_fun hh (ShortAffineJacobian318.x A B)
      simpa only [AlgHom.comp_apply,tangentMap_x,ChartNegation318.affineNeg_x,
        x3,map_sub,map_pow,x1,x2,TangentDiagonal318.diagonal_left,
        TangentDiagonal318.diagonal_right] using hx
    · have hy:=AlgHom.congr_fun hh (ShortAffineJacobian318.y A B)
      simpa only [AlgHom.comp_apply,tangentMap_y,ChartNegation318.affineNeg_y,
        y3,x3,map_sub,map_mul,map_pow,map_neg,x1,x2,y1,TangentDiagonal318.diagonal_left,
        TangentDiagonal318.diagonal_right] using hy

end ThreeTorsionTangent318
