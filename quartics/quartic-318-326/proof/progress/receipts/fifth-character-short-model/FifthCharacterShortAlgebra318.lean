module
public import FifthCharacterShortPolynomial318
public import UnitRootScaling318
public import AffineCoordinateDomain318
public section
noncomputable section
namespace FifthCharacterShortAlgebra318
open Polynomial QuadraticPresentation318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev CubicRing:=RootRing FifthCharacterPolynomial318.reciprocal
abbrev ShortRoot:=RootRing shortPolynomial
@[expose] def changeBase:CubicRing≃ₐ[ℚ]RootRing (baseChange FifthCharacterPolynomial318.reciprocal):=
  AdjoinRoot.mapAlgEquiv baseChange (polynomial FifthCharacterPolynomial318.reciprocal)
    (polynomial (baseChange FifthCharacterPolynomial318.reciprocal)) (by
      simp only [polynomial,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
      exact Associated.refl _)
@[expose] def rootScale:ℚ[X]ˣ:=Units.map Polynomial.C.toMonoidHom yScale⁻¹
@[expose] def rootEquiv:CubicRing≃ₐ[ℚ]ShortRoot:=
  changeBase.trans ((UnitRootScaling318.equiv _ _ rootScale changed_reciprocal).restrictScalars ℚ)
@[expose] def standardEquiv:ShortRoot≃ₐ[ℚ]AffineCoordinateDomain318.CoordinateRing A B:=
  AdjoinRoot.algEquivOfEq ℚ _ _ (AffineCoordinateDomain318.polynomial_formula A B).symm
/-- Actual affine algebra equivalence, with both inverse witnesses from
invertible base/root changes and the specified Weierstrass presentation. -/
@[expose] def coordinateEquiv:CubicRing≃ₐ[ℚ]ShortAffineJacobian318.Ring A B:=
  (rootEquiv.trans standardEquiv).trans (AffineCoordinateDomain318.coordinateEquiv A B).symm
end FifthCharacterShortAlgebra318
