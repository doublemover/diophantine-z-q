module
public import OriginalIntegerRationalNormalization318
public import SourceGlobalAffine318
public section
noncomputable section
namespace OriginalIntegerRationalSourceIdentification318
open AlgebraicGeometry CategoryTheory
open Polynomial
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
open OriginalIntegerRationalNormalization318
abbrev OriginalOrder := ContactKummerOrder318.SourceOrder c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
attribute [local instance] rationalBaseAlgebra

/-- This is the original source embedding into L, not a new field action. -/
local instance originalFieldAlgebra : Algebra (OriginalOrder c) (L c) :=
  OriginalIntegerFractionField318.rationalFieldAlgebra c

/-- Normality of the WHOLE original rational order comes from its proved
four-branch principal cover, not from a generic field or an étale subopen. -/
theorem original_isIntegralClosure :
    IsIntegralClosure (OriginalOrder c) ℚ[X] (L c) :=
  SourceClosureComparison318.source_isIntegralClosure c
    (SourceGlobalAffine318.source_integrallyClosed c)

/-- Identify the normalized rational coefficient chart with the original
entire four-root polynomial order in its specified common fraction field. -/
@[expose] def rationalOrderEquiv : RationalClosure c ≃ₐ[ℚ[X]] OriginalOrder c := by
  letI := original_isIntegralClosure c
  exact IsIntegralClosure.equiv ℚ[X] (RationalClosure c) (L c) (OriginalOrder c)

theorem rationalOrderEquiv_embedding (z : RationalClosure c) :
    ContactKummerOrder318.embedding c (rationalOrderEquiv c z) = z.val := by
  letI := original_isIntegralClosure c
  exact IsIntegralClosure.algebraMap_equiv ℚ[X]
    (RationalClosure c) (L c) (OriginalOrder c) z

/-- The actual integer-normalization rational tensor fiber equals the
original affine four-root source. No denominator in the parameter is used. -/
@[expose] def integerRationalFiberOrderEquiv :
    IntegerClosure c ⊗[ℤ] ℚ ≃+* OriginalOrder c :=
  (integerRationalFiberEquiv c).toRingEquiv.trans (rationalOrderEquiv c).toRingEquiv

/-- A literal affine chart of the original normalized projective contact
curve, reached from the integer-normalization rational fiber ring. -/
@[expose] def rationalFiberSourceIso :
    Spec (CommRingCat.of (IntegerClosure c ⊗[ℤ] ℚ)) ≅
      Spec (CommRingCat.of (OriginalOrder c)) :=
  Scheme.Spec.mapIso (integerRationalFiberOrderEquiv c).symm.toCommRingCatIso.op

@[expose] def rationalFiberChart :
    Spec (CommRingCat.of (IntegerClosure c ⊗[ℤ] ℚ)) ⟶
      (ContactProjectiveModel318.coverMap c).normalization :=
  (rationalFiberSourceIso c).hom ≫ SourceGlobalAffine318.chartEmbedding c

instance rationalFiberChart_open : IsOpenImmersion (rationalFiberChart c) := by
  unfold rationalFiberChart
  infer_instance

theorem rationalFiberChart_range :
    (rationalFiberChart c).opensRange = (SourceGlobalAffine318.actualOpen c).1 := by
  change ((rationalFiberSourceIso c).hom ≫ SourceGlobalAffine318.chartEmbedding c).opensRange = _
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (SourceGlobalAffine318.chartEmbedding_range c)

end OriginalIntegerRationalSourceIdentification318
