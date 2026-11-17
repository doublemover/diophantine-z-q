module
public import OriginalIntegerReciprocalRationalParameter318
public import SourceNormalChart318
public import InfinityGlobalChart318
public import NormalizationBaseCompatibility318
public section
noncomputable section
namespace OriginalIntegerRationalReciprocalChart318
open AlgebraicGeometry CategoryTheory
open Polynomial
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
open OriginalIntegerReciprocalRationalNormalization318
abbrev OriginalOpenOrder := ContactKummerOrder318.OpenOrder c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
attribute [local instance] rationalBaseAlgebra

@[expose] def originalCoefficientAlgebra : Algebra ℚ[X] (OriginalOpenOrder c) :=
  (ContactReciprocalCover318.polynomialMap (OriginalOpenOrder c)).toAlgebra
attribute [local instance] originalCoefficientAlgebra
local instance originalFieldAlgebra : Algebra (OriginalOpenOrder c) (L c) :=
  (SourceOpenFractionField318.openEmbedding c).toAlgebra
local instance originalDomain : IsDomain (OriginalOpenOrder c) :=
  ContactKummerOpenDomain318.open_domain c
local instance originalNormal : IsIntegrallyClosed (OriginalOpenOrder c) :=
  SourceNormalChart318.source_integrallyClosed c
local instance originalFraction : IsFractionRing (OriginalOpenOrder c) (L c) :=
  SourceOpenFractionField318.open_fractionField c
local instance originalTower : @IsScalarTower ℚ[X] (OriginalOpenOrder c) (L c)
    (originalCoefficientAlgebra c).toSMul (originalFieldAlgebra c).toSMul
    (rationalBaseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ[X]) (S := OriginalOpenOrder c) (A := L c)
    (OriginalIntegerReciprocalRationalParameter318.reciprocal_polynomial_square c)

/-- The whole original normalization chart over the reciprocal polynomial
base. This is NOT the smaller previously chosen infinity neighborhood. -/
abbrev OriginalClosure := integralClosure ℚ[X] (OriginalOpenOrder c)

theorem originalClosure_isIntegralClosure :
    IsIntegralClosure (OriginalClosure c) ℚ[X] (L c) :=
  IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    ℚ[X] (OriginalClosure c) (OriginalOpenOrder c) (L c)

@[expose] def rationalClosureEquiv : RationalClosure c ≃ₐ[ℚ[X]] OriginalClosure c := by
  letI := originalClosure_isIntegralClosure c
  exact IsIntegralClosure.equiv ℚ[X] (RationalClosure c) (L c) (OriginalClosure c)

/-- The comparison preserves the specified embedding in the ORIGINAL L. -/
theorem rationalClosureEquiv_embedding (z : RationalClosure c) :
    SourceOpenFractionField318.openEmbedding c (rationalClosureEquiv c z).val = z.val := by
  letI := originalClosure_isIntegralClosure c
  exact IsIntegralClosure.algebraMap_equiv ℚ[X]
    (RationalClosure c) (L c) (OriginalClosure c) z

@[expose] def actualOpen : (ContactProjectiveModel318.coverMap c).normalization.affineOpens :=
  ⟨(ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ
      (JLineAtlas318.chart ℚ 0 ''ᵁ ⊤),
    (NormalizationBaseCompatibility318.target_affine (JLineAtlas318.chart ℚ 0)).preimage _⟩

@[expose] def chartRing : CommRingCat :=
  Γ((ContactProjectiveModel318.coverMap c).normalization, (actualOpen c).1)

@[expose] def sectionsEquiv : chartRing c ≃+* OriginalClosure c :=
  InfinityGlobalChart318.sectionsEquiv_of_factor
    (CommRingCat.ofHom (ContactReciprocalCover318.polynomialMap (OriginalOpenOrder c)))
    (JLineAtlas318.chart ℚ 0) (ContactProjectiveModel318.coverMap c)
    (ContactGlobalProper318.reciprocal_factor c)

/-- The actual reciprocal tensor fiber equals the sections of the WHOLE
reciprocal chart of the original projective contact normalization. -/
@[expose] def fiberSectionsEquiv : IntegerClosure c ⊗[ℤ] ℚ ≃+* chartRing c :=
  (integerRationalFiberEquiv c).toRingEquiv.trans
    ((rationalClosureEquiv c).toRingEquiv.trans (sectionsEquiv c).symm)

@[expose] def fiberChartIso : Spec (CommRingCat.of (IntegerClosure c ⊗[ℤ] ℚ)) ≅
    Spec (chartRing c) :=
  Scheme.Spec.mapIso (fiberSectionsEquiv c).symm.toCommRingCatIso.op

@[expose] def fiberChart : Spec (CommRingCat.of (IntegerClosure c ⊗[ℤ] ℚ)) ⟶
    (ContactProjectiveModel318.coverMap c).normalization :=
  (fiberChartIso c).hom ≫ (actualOpen c).2.fromSpec

instance fiberChart_open : IsOpenImmersion (fiberChart c) := by
  unfold fiberChart
  infer_instance

theorem fiberChart_range : (fiberChart c).opensRange = (actualOpen c).1 := by
  change ((fiberChartIso c).hom ≫ (actualOpen c).2.fromSpec).opensRange = _
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (actualOpen c).2.opensRange_fromSpec

end OriginalIntegerRationalReciprocalChart318
