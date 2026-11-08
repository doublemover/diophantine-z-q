module
public import NonverticalDoubling318
public section
noncomputable section
namespace ThreeTorsionOpenUniversal318
open NonverticalDoubling318 ThreeTorsionScheme318 ThreeTorsionAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

/-- The actual rank-eight algebra is a coequalizer of the two actual
coordinate maps from the affine curve to its nonvertical open. -/
theorem existsUnique {S:Type} [CommRing S] [Algebra R S] (k:OpenRing A B→ₐ[R]S)
    (hk:k.comp (double A B)=k.comp (negative A B)) :
    ∃! ψ:Ring A B hD→ₐ[R]S,ψ.comp (toTorsion A B hD)=k:=by
  let φ:=k.comp (curveMap A B)
  have hu:IsUnit (2*φ (ShortAffineJacobian318.y A B)):=by
    simpa only [φ,map_mul,map_ofNat,AlgHom.comp_apply] using (unit A B).map k
  have hn:=TangentDiagonalNatural318.natural A B (curveMap A B) k (unit A B) hu
  have he:(TangentDiagonal318.diagonal A B φ hu).comp (TangentOpenAlgebra318.tangentMap A B)=
      φ.comp (ChartNegation318.affineNeg A B):=by
    unfold double negative at hk
    rw [←AlgHom.comp_assoc,hn,←AlgHom.comp_assoc] at hk
    exact hk
  obtain ⟨ψ,hψ,hunique⟩:=(ThreeTorsionTangentUniversal318.universal A B hD φ hu).mp he
  refine ⟨ψ,?_,?_⟩
  · apply IsLocalization.algHom_ext (Submonoid.powers (denominator A B))
    change (ψ.comp (toTorsion A B hD)).comp (curveMap A B)=k.comp (curveMap A B)
    rw [AlgHom.comp_assoc,toTorsion_curveMap]
    exact hψ
  · intro χ hχ
    apply hunique
    calc
      χ.comp (coordinateMap A B hD)=(χ.comp (toTorsion A B hD)).comp (curveMap A B):=by
        rw [AlgHom.comp_assoc,toTorsion_curveMap]
      _ = φ := by rw [hχ]

end ThreeTorsionOpenUniversal318
