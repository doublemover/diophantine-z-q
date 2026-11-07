module
public import InfinityAdditionFinite318
public section
noncomputable section
namespace FiniteCrossMaps318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Actual finite chord and tangent quotient maps agree on every common coefficient algebra
with the same genuine input pair. -/
theorem output_maps_agree (A B:R) (f:RelativeChordAlgebra318.ChordRing A B →ₐ[R] S)
    (g:TangentOpenAlgebra318.TangentRing A B →ₐ[R] S)
    (hp:∀a:PairRing A B, f (TangentChordOverlap318.chordPairMap A B a)=
      g (TangentChordOverlap318.tangentPairMap A B a)) :
    f.comp (RelativeChordAlgebra318.chordMap A B)=g.comp (TangentOpenAlgebra318.tangentMap A B) := by
  have hl (a:ShortAffineJacobian318.Ring A B) : f (RelativeChordAlgebra318.left A B a)=g (TangentOpenAlgebra318.left A B a):=hp _
  have hr (a:ShortAffineJacobian318.Ring A B) : f (RelativeChordAlgebra318.right A B a)=g (TangentOpenAlgebra318.right A B a):=hp _
  have h1:=congrArg f (RelativeChordAlgebra318.slope_identity A B)
  have h2:=congrArg g (TangentOpenAlgebra318.slope_gap A B)
  simp only [map_mul,map_sub,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,
    RelativeChordAlgebra318.y1,RelativeChordAlgebra318.y2,hl,hr] at h1
  simp only [map_mul,map_sub,TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,
    TangentOpenAlgebra318.y1,TangentOpenAlgebra318.y2] at h2
  have hu:IsUnit (g (TangentOpenAlgebra318.x2 A B)-g (TangentOpenAlgebra318.x1 A B)) := by
    have hh:=(RelativeChordAlgebra318.gap_unit A B).map f
    simpa only [map_sub,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,
      TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,hl,hr] using hh
  have hs:f (RelativeChordAlgebra318.slope A B)=g (TangentOpenAlgebra318.slope A B):=
    hu.mul_right_cancel (h1.trans h2.symm)
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,RelativeChordAlgebra318.chordMap_x,TangentOpenAlgebra318.tangentMap_x,
      RelativeChordAlgebra318.x3,TangentOpenAlgebra318.x3,map_sub,map_pow,hs,
      RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,hl,hr]
  · simp only [AlgHom.comp_apply,RelativeChordAlgebra318.chordMap_y,TangentOpenAlgebra318.tangentMap_y,
      RelativeChordAlgebra318.y3,TangentOpenAlgebra318.y3,RelativeChordAlgebra318.x3,TangentOpenAlgebra318.x3,
      map_sub,map_mul,map_pow,hs,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,RelativeChordAlgebra318.y1,
      TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,TangentOpenAlgebra318.y1,hl,hr]

open AlgebraicGeometry CategoryTheory in
theorem scheme_agreement (A B:R) (f:RelativeChordAlgebra318.ChordRing A B →ₐ[R] S)
    (g:TangentOpenAlgebra318.TangentRing A B →ₐ[R] S)
    (hp:∀a:PairRing A B, f (TangentChordOverlap318.chordPairMap A B a)=
      g (TangentChordOverlap318.tangentPairMap A B a)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ RelativeChordScheme318.addition A B=
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ TangentOpenScheme318.addition A B := by
  dsimp only [RelativeChordScheme318.addition,RelativeChordScheme318.chordOpen,
    TangentOpenScheme318.addition,TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (output_maps_agree A B f g hp))

end FiniteCrossMaps318
