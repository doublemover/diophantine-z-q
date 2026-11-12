module
public import ThreeBranchLegendrePolynomial318
public import UnitRootScaling318
public import AffineCoordinateDomain318
public section
noncomputable section
namespace ThreeBranchLegendreAffineIso318
open Polynomial QuadraticPresentation318 ThreeBranchLegendrePolynomial318
open AlgebraicGeometry CategoryTheory
variable (a b c:ℂ) (hab:b≠a)
abbrev Cubic:=RootRing (cubic a b c)
abbrev Short:=RootRing (shortPolynomial a b c)

@[expose] def changeBase:Cubic a b c≃ₐ[ℂ]
    RootRing (baseChange a b c hab (cubic a b c)):=
  AdjoinRoot.mapAlgEquiv (baseChange a b c hab) (polynomial (cubic a b c))
    (polynomial (baseChange a b c hab (cubic a b c))) (by
      simp only [polynomial,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
      exact Associated.refl _)
@[expose] def rootEquiv:Cubic a b c≃ₐ[ℂ]Short a b c:=
  (changeBase a b c hab).trans
    ((UnitRootScaling318.equiv _ _ (scaleUnit a b hab)
      (scaled_cubic a b c hab)).restrictScalars ℂ)
/-- Both coordinate formulas retain the explicit root scale and the whole
polynomial base substitution before passing to the Weierstrass presentation. -/
lemma rootEquiv_root:rootEquiv a b c hab (AdjoinRoot.root (polynomial (cubic a b c)))=
    algebraMap ℂ[X] (Short a b c) (scaleUnit a b hab:ℂ[X])*
      AdjoinRoot.root (polynomial (shortPolynomial a b c)):=by
  simp only [rootEquiv,AlgEquiv.trans_apply,changeBase,AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_root]
  exact UnitRootScaling318.hom_root _ _ _ _

lemma rootEquiv_polynomial (p:ℂ[X]):rootEquiv a b c hab
    (algebraMap ℂ[X] (Cubic a b c) p)=
      algebraMap ℂ[X] (Short a b c) (baseChange a b c hab p):=by
  simp only [rootEquiv,AlgEquiv.trans_apply,changeBase,AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.algebraMap_eq,AdjoinRoot.map_of]
  exact (UnitRootScaling318.equiv _ _ (scaleUnit a b hab)
    (scaled_cubic a b c hab)).commutes _

@[expose] def standardEquiv:Short a b c≃ₐ[ℂ]
    AffineCoordinateDomain318.CoordinateRing
      (NormalizedLegendreProjectiveModel318.A (parameter a b c))
      (NormalizedLegendreProjectiveModel318.B (parameter a b c)):=
  AdjoinRoot.algEquivOfEq ℂ _ _
    (AffineCoordinateDomain318.polynomial_formula _ _).symm

/-- A genuine equivalence of the whole cubic coordinate algebra with the
correctly normalized affine Legendre model. The root scale is explicit. -/
@[expose] def coordinateEquiv:Cubic a b c≃ₐ[ℂ]
    ShortAffineJacobian318.Ring
      (NormalizedLegendreProjectiveModel318.A (parameter a b c))
      (NormalizedLegendreProjectiveModel318.B (parameter a b c)):=
  ((rootEquiv a b c hab).trans (standardEquiv a b c)).trans
    (AffineCoordinateDomain318.coordinateEquiv _ _).symm

/-- The whole original cubic scheme is isomorphic to this exact finite
chart of the independently constructed proper normalized Legendre curve. -/
@[expose] def affineIso:ShortAffineScheme318.scheme
    (NormalizedLegendreProjectiveModel318.A (parameter a b c))
    (NormalizedLegendreProjectiveModel318.B (parameter a b c))≅
    Spec (CommRingCat.of (Cubic a b c)):=
  Scheme.Spec.mapIso (coordinateEquiv a b c hab).toRingEquiv.toCommRingCatIso.op

theorem over_complex:(affineIso a b c hab).hom≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Cubic a b c)))=
    ShortAffineScheme318.structureMap
      (NormalizedLegendreProjectiveModel318.A (parameter a b c))
      (NormalizedLegendreProjectiveModel318.B (parameter a b c)):=by
  change Spec.map (CommRingCat.ofHom (coordinateEquiv a b c hab).toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (coordinateEquiv a b c hab).commutes z
end ThreeBranchLegendreAffineIso318
