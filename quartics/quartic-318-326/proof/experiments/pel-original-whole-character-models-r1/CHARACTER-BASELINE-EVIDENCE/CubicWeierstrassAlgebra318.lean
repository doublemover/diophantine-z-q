module
public import UnitRootScaling318
public import CubicWeierstrassPolynomial318
public import AffineCoordinateDomain318
public section
noncomputable section
namespace CubicWeierstrassAlgebra318
open Polynomial QuadraticPresentation318 CubicWeierstrassPolynomial318 SourceTwistArithmetic318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev CubicRing (i:Fin 4):=RootRing (radicand i)
abbrev ShortRoot (i:Fin 4):=RootRing (shortPolynomial i)

@[expose] def changeBase (i:Fin 4):CubicRing i≃ₐ[ℚ]RootRing (baseChange i (radicand i)):=
  AdjoinRoot.mapAlgEquiv (baseChange i) (polynomial (radicand i))
    (polynomial (baseChange i (radicand i))) (by
      simp only [polynomial,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
      exact Associated.refl _)
@[expose] def scaleUnit (i:Fin 4):ℚ[X]ˣ:=
  Units.map Polynomial.C.toMonoidHom (twistUnit i)⁻¹

/-- Actual rational algebra equivalence from the literal twisted cubic
root presentation to the literal short Weierstrass root presentation. -/
@[expose] def rootEquiv (i:Fin 4):CubicRing i≃ₐ[ℚ]ShortRoot i:=
  (changeBase i).trans ((UnitRootScaling318.equiv _ _ (scaleUnit i)
    (changed_radicand i)).restrictScalars ℚ)

@[expose] def standardEquiv (i:Fin 4):ShortRoot i≃ₐ[ℚ]
    AffineCoordinateDomain318.CoordinateRing (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i):=
  AdjoinRoot.algEquivOfEq ℚ _ _
    (AffineCoordinateDomain318.polynomial_formula
      (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)).symm

/-- The complete affine cubic-to-short comparison on actual quotient
coordinate algebras, not only a match of equations or j-invariants. -/
@[expose] def coordinateEquiv (i:Fin 4):CubicRing i≃ₐ[ℚ]
    ShortAffineJacobian318.Ring (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i):=
  ((rootEquiv i).trans (standardEquiv i)).trans
    (AffineCoordinateDomain318.coordinateEquiv
      (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)).symm
end CubicWeierstrassAlgebra318
