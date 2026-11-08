module
public import FifthCharacterOrder318
public import UnitRootScaling318
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace FifthCharacterReciprocal318
open Polynomial QuadraticPresentation318 FifthCharacterPolynomial318
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Laurent := LaurentPolynomial ℚ
abbrev QuarticOpen := RootRing (algebraMap ℚ[X] Laurent quartic)
abbrev CubicOpen := RootRing (algebraMap ℚ[X] Laurent reciprocal)
@[expose] def inverseSquare : Laurentˣ :=
  (LaurentPolynomial.isUnit_T (-2)).unit
lemma inverseSquare_val : (inverseSquare:Laurent)=LaurentPolynomial.T (-2) :=
  (LaurentPolynomial.isUnit_T (-2)).unit_spec

/-- Exact Laurent identity under inversion of the base coordinate. -/
theorem inversion_relation :
    LaurentPolynomial.invert (algebraMap ℚ[X] Laurent quartic)=
      algebraMap ℚ[X] Laurent reciprocal*(inverseSquare:Laurent)^2 := by
  have h: (LaurentPolynomial.T (-1):Laurent)*LaurentPolynomial.T 1=1 := by
    rw [←LaurentPolynomial.T_add]; norm_num
  have h2: (inverseSquare:Laurent)=LaurentPolynomial.T (-1)*LaurentPolynomial.T (-1) := by
    rw [inverseSquare_val,←LaurentPolynomial.T_add]; rfl
  simp only [quartic,reciprocal,map_mul,map_sub,map_add,map_one,
    LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_C,Polynomial.toLaurent_X,
    LaurentPolynomial.invert_C,LaurentPolynomial.invert_T]
  rw [h2]
  have he (a:Laurent):LaurentPolynomial.T (-1)-a=
      (1-a*LaurentPolynomial.T 1)*LaurentPolynomial.T (-1) := by
    linear_combination a*h
  have hp (a:Laurent):LaurentPolynomial.T (-1)+a=
      (1+a*LaurentPolynomial.T 1)*LaurentPolynomial.T (-1) := by
    linear_combination -a*h
  rw [he,he,hp]
  ring

@[expose] def invertBase : QuarticOpen ≃ₐ[ℚ]
    RootRing (LaurentPolynomial.invert (algebraMap ℚ[X] Laurent quartic)) :=
  AdjoinRoot.mapAlgEquiv LaurentPolynomial.invert _ _ (by
    simp only [polynomial,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
    exact Associated.refl _)

/-- Actual inverse-coordinate comparison, only after inverting the base
parameter on both sides. It is not an isomorphism of the two whole affine curves. -/
@[expose] def equiv : QuarticOpen ≃ₐ[ℚ] CubicOpen :=
  invertBase.trans ((UnitRootScaling318.equiv _ _ inverseSquare inversion_relation).restrictScalars ℚ)

@[expose] def quarticBaseChange : Laurent⊗[ℚ[X]]FifthCharacterOrder318.Order ≃ₐ[Laurent]QuarticOpen :=
  ContactGenericFiber318.rootBaseChange quartic
@[expose] def cubicBaseChange : Laurent⊗[ℚ[X]]RootRing reciprocal ≃ₐ[Laurent]CubicOpen :=
  ContactGenericFiber318.rootBaseChange reciprocal

/-- The actual two localized scalar extensions, with an explicit two-sided inverse. -/
@[expose] def tensorEquiv : Laurent⊗[ℚ[X]]FifthCharacterOrder318.Order ≃ₐ[ℚ]
    Laurent⊗[ℚ[X]]RootRing reciprocal :=
  (quarticBaseChange.restrictScalars ℚ).trans (equiv.trans
    (cubicBaseChange.symm.restrictScalars ℚ))
end FifthCharacterReciprocal318
