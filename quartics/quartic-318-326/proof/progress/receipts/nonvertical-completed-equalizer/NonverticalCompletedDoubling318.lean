module
public import CompletedTangentRestriction318
public import ThreeTorsionEqualizerScheme318
public import GluedNegation318
public section
noncomputable section
namespace NonverticalCompletedDoubling318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NonverticalDoubling318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type} [CommRing R] (A B:R)

@[expose] def diagonal : Spec (CommRingCat.of (OpenRing A B))⟶TangentOpenScheme318.tangentOpen A B :=
  Spec.map (CommRingCat.ofHom (TangentDiagonal318.diagonal A B (curveMap A B) (unit A B)).toRingHom)

lemma diagonal_intoProduct : diagonal A B ≫ TangentOpenScheme318.intoProduct A B =
    pullback.lift (ThreeTorsionEqualizerScheme318.openInclusion A B)
      (ThreeTorsionEqualizerScheme318.openInclusion A B) rfl := by
  apply pullback.hom_ext
  · rw [Category.assoc,TangentOpenScheme318.intoProduct_fst,pullback.lift_fst]
    dsimp only [diagonal,ThreeTorsionEqualizerScheme318.openInclusion,
      TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
    rw [←Spec.map_comp]
    have hh : (TangentDiagonal318.diagonal A B (curveMap A B) (unit A B)).comp
        (TangentOpenAlgebra318.left A B)=curveMap A B :=
      AlgHom.ext (fun z=>TangentDiagonal318.diagonal_left A B (curveMap A B) (unit A B) z)
    exact congrArg (fun f:Curve A B→ₐ[R]OpenRing A B => Spec.map (CommRingCat.ofHom f.toRingHom)) hh
  · rw [Category.assoc,TangentOpenScheme318.intoProduct_snd,pullback.lift_snd]
    dsimp only [diagonal,ThreeTorsionEqualizerScheme318.openInclusion,
      TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
    rw [←Spec.map_comp]
    have hh : (TangentDiagonal318.diagonal A B (curveMap A B) (unit A B)).comp
        (TangentOpenAlgebra318.right A B)=curveMap A B :=
      AlgHom.ext (fun z=>TangentDiagonal318.diagonal_right A B (curveMap A B) (unit A B) z)
    exact congrArg (fun f:Curve A B→ₐ[R]OpenRing A B => Spec.map (CommRingCat.ofHom f.toRingHom)) hh

lemma diagonal_addition : diagonal A B ≫ TangentOpenScheme318.addition A B =
    ThreeTorsionEqualizerScheme318.doubling A B := by
  dsimp only [diagonal,TangentOpenScheme318.addition,ThreeTorsionEqualizerScheme318.doubling,
    TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp]
  rfl

@[expose] def intoCompleted : Spec (CommRingCat.of (OpenRing A B))⟶WeierstrassGluing318.scheme A B :=
  ThreeTorsionEqualizerScheme318.openInclusion A B ≫ WeierstrassGluing318.finiteChart A B

/-- Exact equality with the actual completed doubling restriction on D(2y). -/
theorem doubling_restriction (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    intoCompleted A B ≫ CompletedIteratedAddition318.doubling A B hD =
      ThreeTorsionEqualizerScheme318.doubling A B ≫ WeierstrassGluing318.finiteChart A B := by
  rw [intoCompleted,Category.assoc,CompletedTangentRestriction318.doubling_restriction A B hD
    (ThreeTorsionEqualizerScheme318.openInclusion A B) (diagonal A B) (diagonal_intoProduct A B),
    ←Category.assoc,diagonal_addition]

lemma affine_negation : ThreeTorsionEqualizerScheme318.openInclusion A B ≫
    GluedNegation318.finiteNeg A B = ThreeTorsionEqualizerScheme318.negation A B := by
  dsimp only [ThreeTorsionEqualizerScheme318.openInclusion,GluedNegation318.finiteNeg,
    ThreeTorsionEqualizerScheme318.negation,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp]
  rfl

/-- Exact equality with global negation restricted along the same actual open inclusion. -/
theorem negation_restriction : intoCompleted A B ≫ GluedNegation318.negation A B =
    ThreeTorsionEqualizerScheme318.negation A B ≫ WeierstrassGluing318.finiteChart A B := by
  rw [intoCompleted,Category.assoc,GluedNegation318.finiteChart_negation,
    ←Category.assoc,affine_negation]
end NonverticalCompletedDoubling318
