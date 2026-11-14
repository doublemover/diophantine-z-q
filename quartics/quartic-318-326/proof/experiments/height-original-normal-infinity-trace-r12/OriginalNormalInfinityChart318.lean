module
public import OriginalNormalInfinityOrder318
public section
noncomputable section
namespace OriginalNormalInfinityChart318
open AlgebraicGeometry CategoryTheory NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalInfinityOrder318 IntegralDistinctContactOpen318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "B" => SourceOpenRing c t w D
local notation "δ" => arithmeticDenominator R D.coefficients
local notation "C" => Order c t w D
local instance sourceDomain : IsDomain B :=
  open_domain R a D.coefficients (K c t) (IsFractionRing.injective R (K c t))
    (contacts_injective c t w) (coefficients_ne_zero c t w D)
local instance : Module.Finite (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).1
local instance : Algebra.Etale (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).2.2

@[expose] def canonicalData :
    NormalizationClosureChart318.Data (A:=CommRingCat.of R[X])
      (B:=CommRingCat.of B) (C:=CommRingCat.of C)
      (inclusion c t w D) (polynomialScalar c t w D)
      (IntegralTwoChartNormalization318.coverMap R a δ B) (JLineAtlas318.chart R 0) :=
  NormalizationClosureChart318.data (CommRingCat.ofHom (polynomialMap c t w D))
    (JLineAtlas318.chart R 0) (IntegralTwoChartNormalization318.coverMap R a δ B)
    (IntegralTwoChartNormalization318.reciprocal_factor R a δ B)

/-- The whole reciprocal integral closure is an actual open chart of
SAME original normal M, with the same canonical normalization isomorphism. -/
@[expose] def chart : Spec (CommRingCat.of C) ⟶ M.scheme :=
  (canonicalData c t w D).chart ≫ (OriginalNormalModelCanonicalIso318.iso c t w D M).hom
instance chart_open : IsOpenImmersion (chart c t w D M) := by
  letI := (canonicalData c t w D).isOpen
  unfold chart
  infer_instance

@[reassoc] lemma source : Spec.map (CommRingCat.ofHom (inclusion c t w D)) ≫
    chart c t w D M=M.source := by
  unfold chart
  rw [←Category.assoc,(canonicalData c t w D).source]
  exact OriginalNormalModelCanonicalIso318.source c t w D M

@[reassoc] lemma base : chart c t w D M ≫ M.projection=
    Spec.map (CommRingCat.ofHom (polynomialScalar c t w D)) ≫ JLineAtlas318.chart R 0 := by
  unfold chart
  rw [Category.assoc,OriginalNormalModelCanonicalIso318.base]
  exact (canonicalData c t w D).base

@[reassoc] lemma structure : chart c t w D M ≫ M.structureMap=
    Spec.map (CommRingCat.ofHom (scalar c t w D)) := by
  change chart c t w D M ≫ M.projection ≫ ProjectiveJLine318.structureMap R=_
  rw [←Category.assoc,base,Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
  rfl
end OriginalNormalInfinityChart318
