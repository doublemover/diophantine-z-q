module
public import ThreeTorsionTangentUniversal318
public section
noncomputable section
namespace ThreeTorsionTangentScheme318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ThreeTorsionAlgebra318 ThreeTorsionScheme318 TangentOpenScheme318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

lemma ordinate_unit : IsUnit (2*coordinateMap A B hD (ShortAffineJacobian318.y A B)):=by
  rw [coordinateMap_y]
  apply IsUnit.mul _ (y_unit A B hD)
  simpa only [map_ofNat] using (two_unit A B hD).map (algebraMap R (Ring A B hD))

@[expose] def diagonalMap : TangentOpenAlgebra318.TangentRing A B→ₐ[R]Ring A B hD :=
  TangentDiagonal318.diagonal A B (coordinateMap A B hD) (ordinate_unit A B hD)

lemma double_neg_coordinates :
    (diagonalMap A B hD).comp (TangentOpenAlgebra318.tangentMap A B)=
      (coordinateMap A B hD).comp (ChartNegation318.affineNeg A B):=by
  apply (ThreeTorsionTangent318.factor_iff_double_neg A B (coordinateMap A B hD)
    (ordinate_unit A B hD)).mp
  rw [coordinateMap_x]
  exact ThreeTorsionFunctor318.x_relation A B hD

/-- The actual rank-eight torsion scheme lies in the nonvertical diagonal
open; the invertibility of 2y is proved from its equation algebra. -/
@[expose] def diagonal : scheme A B hD⟶tangentOpen A B :=
  Spec.map (CommRingCat.ofHom (diagonalMap A B hD).toRingHom)

/-- Equality of actual Scheme morphisms on the entire relative torsion
scheme, not only equality of their geometric-point values. -/
theorem double_neg : diagonal A B hD≫addition A B=
    inclusion A B hD≫Spec.map (CommRingCat.ofHom (ChartNegation318.affineNeg A B).toRingHom):=by
  dsimp only [diagonal,addition,inclusion,scheme,tangentOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:ShortAffineJacobian318.Ring A B→ₐ[R]Ring A B hD=>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (double_neg_coordinates A B hD)

/-- Its two actual product projections are both the original inclusion. -/
theorem diagonal_intoProduct : diagonal A B hD≫intoProduct A B=
    pullback.lift (inclusion A B hD) (inclusion A B hD) rfl := by
  apply pullback.hom_ext
  · rw [Category.assoc,intoProduct_fst,pullback.lift_fst]
    dsimp only [diagonal,inclusion,scheme,tangentOpen,ShortAffineScheme318.scheme]
    rw [←Spec.map_comp]
    have hh:(diagonalMap A B hD).comp (TangentOpenAlgebra318.left A B)=coordinateMap A B hD:=
      AlgHom.ext (fun z=>TangentDiagonal318.diagonal_left A B
        (coordinateMap A B hD) (ordinate_unit A B hD) z)
    exact congrArg (fun f:ShortAffineJacobian318.Ring A B→ₐ[R]Ring A B hD=>
      Spec.map (CommRingCat.ofHom f.toRingHom)) hh
  · rw [Category.assoc,intoProduct_snd,pullback.lift_snd]
    dsimp only [diagonal,inclusion,scheme,tangentOpen,ShortAffineScheme318.scheme]
    rw [←Spec.map_comp]
    have hh:(diagonalMap A B hD).comp (TangentOpenAlgebra318.right A B)=coordinateMap A B hD:=
      AlgHom.ext (fun z=>TangentDiagonal318.diagonal_right A B
        (coordinateMap A B hD) (ordinate_unit A B hD) z)
    exact congrArg (fun f:ShortAffineJacobian318.Ring A B→ₐ[R]Ring A B hD=>
      Spec.map (CommRingCat.ofHom f.toRingHom)) hh

end ThreeTorsionTangentScheme318
