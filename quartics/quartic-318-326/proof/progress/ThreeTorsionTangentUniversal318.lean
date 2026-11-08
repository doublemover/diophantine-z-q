module
public import ThreeTorsionTangent318
public section
noncomputable section
namespace ThreeTorsionTangentUniversal318
open Polynomial ThreeTorsionScheme318 ThreeTorsionAlgebra318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} {S:Type*} [CommRing R] [CommRing S] [Algebra R S] (A B:R)
  [Invertible (3:R)] (hD:IsUnit (-16*(4*A^3+27*B^2)))
  (φ:ShortAffineJacobian318.Ring A B→ₐ[R]S)

theorem factor_iff_existsUnique :
    (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R S)
      (φ (ShortAffineJacobian318.x A B))=0 ↔
    ∃! ψ:Ring A B hD→ₐ[R]S,ψ.comp (coordinateMap A B hD)=φ := by
  constructor
  · intro hx
    let p:ThreeTorsionFunctor318.Solutions (S:=S) A B :=
      ⟨(φ (ShortAffineJacobian318.x A B),φ (ShortAffineJacobian318.y A B)),
        hx,TangentDiagonal318.curve_relation A B φ⟩
    refine ⟨ThreeTorsionFunctor318.toHom A B hD p,?_,?_⟩
    · apply WeierstrassOverlap318.affine_hom_ext
      · simp only [AlgHom.comp_apply,coordinateMap_x,ThreeTorsionFunctor318.toHom_x];rfl
      · simp only [AlgHom.comp_apply,coordinateMap_y,ThreeTorsionFunctor318.toHom_y];rfl
    · intro ψ hψ
      apply ThreeTorsionFunctor318.hom_ext
      · have hh:=AlgHom.congr_fun hψ (ShortAffineJacobian318.x A B)
        simpa only [AlgHom.comp_apply,coordinateMap_x,ThreeTorsionFunctor318.toHom_x]
          using hh
      · have hh:=AlgHom.congr_fun hψ (ShortAffineJacobian318.y A B)
        simpa only [AlgHom.comp_apply,coordinateMap_y,ThreeTorsionFunctor318.toHom_y]
          using hh
  · rintro ⟨ψ,hψ,_⟩
    have hh:=AlgHom.congr_fun hψ (ShortAffineJacobian318.x A B)
    simp only [AlgHom.comp_apply,coordinateMap_x] at hh
    rw [←hh]
    exact (ThreeTorsionFunctor318.ofHom A B hD ψ).property.1

/-- Scheme-theoretic universal property on the actual nonvertical diagonal:
all coefficient algebras, not just geometric points, factor uniquely through
the actual rank-eight algebra exactly when tangent doubling equals negation. -/
theorem universal (hu:IsUnit (2*φ (ShortAffineJacobian318.y A B))) :
    (TangentDiagonal318.diagonal A B φ hu).comp (TangentOpenAlgebra318.tangentMap A B)=
      φ.comp (ChartNegation318.affineNeg A B) ↔
    ∃! ψ:Ring A B hD→ₐ[R]S,ψ.comp (coordinateMap A B hD)=φ := by
  rw [←ThreeTorsionTangent318.factor_iff_double_neg A B φ hu,
    factor_iff_existsUnique]

end ThreeTorsionTangentUniversal318
