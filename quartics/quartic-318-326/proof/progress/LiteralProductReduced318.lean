module
public import GeometricFibers318
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.Submodule
public section
noncomputable section
namespace LiteralProductReduced318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact integral coefficient base is reduced at every level, including
level zero where the localization may be the zero ring. -/
theorem base_reduced (N:ℕ) : _root_.IsReduced (OpenJModel318.Base N):=by
  infer_instance

theorem base_noetherian (N:ℕ) : IsNoetherianRing (OpenJModel318.Base N):=by
  infer_instance

/-- Reducedness of the actual completed literal model follows from flatness
and its already proved geometric fibers, not from a pointwise shortcut. -/
theorem curve_reduced (N:ℕ) : IsReduced (WeierstrassGluing318.literalScheme N):=by
  letI:=base_reduced N
  letI:=base_noetherian N
  letI:=GeometricFibers318.literal_geometrically_integral N
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (WeierstrassGluing318.literalStructureMap N)

theorem curve_noetherian (N:ℕ) : IsLocallyNoetherian (WeierstrassGluing318.literalScheme N):=by
  letI:=base_noetherian N
  exact LocallyOfFiniteType.isLocallyNoetherian (WeierstrassGluing318.literalStructureMap N)

/-- Exact relative pair object used by the global law. -/
theorem pair_reduced (N:ℕ) :
    IsReduced (pullback (WeierstrassGluing318.literalStructureMap N)
      (WeierstrassGluing318.literalStructureMap N)):=by
  letI:=curve_reduced N
  letI:=curve_noetherian N
  letI:=GeometricFibers318.literal_geometrically_integral N
  infer_instance

theorem pair_noetherian (N:ℕ) :
    IsLocallyNoetherian (pullback (WeierstrassGluing318.literalStructureMap N)
      (WeierstrassGluing318.literalStructureMap N)):=by
  letI:=curve_noetherian N
  infer_instance

/-- The literal left-associated relative cube is reduced. This endpoint is
specific to the reduced Noetherian integral coefficient base; it does not
assert a field-point equality principle over arbitrary nilpotent bases. -/
theorem triple_reduced (N:ℕ) :
    IsReduced (pullback
      (pullback.fst (WeierstrassGluing318.literalStructureMap N)
        (WeierstrassGluing318.literalStructureMap N)≫WeierstrassGluing318.literalStructureMap N)
      (WeierstrassGluing318.literalStructureMap N)):=by
  letI:=pair_reduced N
  letI:=pair_noetherian N
  letI:=GeometricFibers318.literal_geometrically_integral N
  infer_instance
end LiteralProductReduced318
