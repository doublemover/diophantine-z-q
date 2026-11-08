module
public import FifthCharacterReciprocal318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace FifthReciprocalCoordinates318
open Polynomial QuadraticPresentation318 FifthCharacterPolynomial318 FifthCharacterReciprocal318
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma equiv_on_base (a:Laurent) :
    equiv (algebraMap Laurent QuarticOpen a)=
      algebraMap Laurent CubicOpen (LaurentPolynomial.invert a) := by
  change UnitRootScaling318.equiv _ _ inverseSquare inversion_relation
    (invertBase (algebraMap Laurent QuarticOpen a))=_
  have hb: invertBase (algebraMap Laurent QuarticOpen a)=
      algebraMap Laurent _ (LaurentPolynomial.invert a) := by
    simp only [invertBase,AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.algebraMap_eq,AdjoinRoot.map_of]
    rfl
  rw [hb,AlgEquiv.commutes]

lemma equiv_root :
    equiv (AdjoinRoot.root (polynomial (algebraMap ℚ[X] Laurent quartic)))=
      algebraMap Laurent CubicOpen (LaurentPolynomial.T (-2))*
        AdjoinRoot.root (polynomial (algebraMap ℚ[X] Laurent reciprocal)) := by
  change UnitRootScaling318.equiv _ _ inverseSquare inversion_relation
    (invertBase (AdjoinRoot.root _))=_
  have hb:invertBase (AdjoinRoot.root (polynomial (algebraMap ℚ[X] Laurent quartic)))=
      AdjoinRoot.root (polynomial (LaurentPolynomial.invert (algebraMap ℚ[X] Laurent quartic))) := by
    simp only [invertBase,AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_root]
  rw [hb]
  exact (UnitRootScaling318.hom_root _ _ inverseSquare inversion_relation).trans (by rw [inverseSquare_val])

/-- The base parameter is inverted, exactly, not up to a selected field automorphism. -/
theorem equiv_parameter :
    equiv (algebraMap Laurent QuarticOpen (LaurentPolynomial.T 1))=
      algebraMap Laurent CubicOpen (LaurentPolynomial.T (-1)) := by
  rw [equiv_on_base,LaurentPolynomial.invert_T]

/-- Conversely the old quartic root is the new cubic root divided by u squared. -/
theorem inverse_root :
    equiv.symm (AdjoinRoot.root (polynomial (algebraMap ℚ[X] Laurent reciprocal)))=
      algebraMap Laurent QuarticOpen (LaurentPolynomial.T (-2))*
        AdjoinRoot.root (polynomial (algebraMap ℚ[X] Laurent quartic)) := by
  apply equiv.injective
  rw [AlgEquiv.apply_symm_apply,map_mul,equiv_on_base,equiv_root,LaurentPolynomial.invert_T]
  norm_num only [neg_neg]
  rw [←mul_assoc,←map_mul,←LaurentPolynomial.T_add]
  norm_num

attribute [local instance] Algebra.TensorProduct.rightAlgebra
abbrev QuarticTensor := Laurent⊗[ℚ[X]]FifthCharacterOrder318.Order
abbrev CubicTensor := Laurent⊗[ℚ[X]]RootRing reciprocal

/-- The scalar extension used above is the actual principal localization
of the original whole quartic order, retaining its entire ring structure. -/
theorem quartic_localization : IsLocalization.Away
    (algebraMap ℚ[X] FifthCharacterOrder318.Order X) QuarticTensor := by
  simpa [Algebra.algebraMapSubmonoid,Submonoid.map_powers] using
    (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid FifthCharacterOrder318.Order (Submonoid.powers (X:ℚ[X]))) QuarticTensor)

theorem cubic_localization : IsLocalization.Away
    (algebraMap ℚ[X] (RootRing reciprocal) X) CubicTensor := by
  simpa [Algebra.algebraMapSubmonoid,Submonoid.map_powers] using
    (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid (RootRing reciprocal) (Submonoid.powers (X:ℚ[X]))) CubicTensor)
end FifthReciprocalCoordinates318
