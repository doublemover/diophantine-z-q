module
public import NormalizationClosureChart318
public import OriginalNormalModelSections318
public section
noncomputable section
namespace OriginalNormalOrderChart318
open AlgebraicGeometry CategoryTheory NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open IntegralDistinctContactOpen318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "B" => SourceOpenRing c t w D
local notation "N" => arithmeticDenominator R D.coefficients
abbrev Order := IntegralFourRootNormalizationConductor318.normalOrder R a D.coefficients
local notation "C" => Order c t w D
local instance sourceDomain : IsDomain B :=
  open_domain R a D.coefficients (K c t) (IsFractionRing.injective R (K c t))
    (contacts_injective c t w) (coefficients_ne_zero c t w D)
local instance : Module.Finite (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).1
local instance : Algebra.Etale (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).2.2

/-- The concrete entire normal order, with both actual inclusion and
polynomial scalar map, is an affine chart of the canonical normalization. -/
@[expose] def canonicalData :
    NormalizationClosureChart318.Data (A:=CommRingCat.of R[X])
      (B:=CommRingCat.of B) (C:=CommRingCat.of C)
      (IntegralFourRootNormalizationConductor318.normalOrder R a D.coefficients).val.toRingHom
      (algebraMap R[X] C) (IntegralTwoChartNormalization318.coverMap R a N B)
      (JLineAtlas318.chart R 1) := by
  have hα : (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B).toAlgebra=
      (inferInstance : Algebra R[X] B) := by
    rw [IntegralNormalizationConductorChart318.scalarMap_eq]
    exact toAlgebra_algebraMap (R:=R[X]) (S:=B)
  have E := NormalizationClosureChart318.data
    (CommRingCat.ofHom (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B))
    (JLineAtlas318.chart R 1) (IntegralTwoChartNormalization318.coverMap R a N B)
    (IntegralTwoChartNormalization318.finite_factor R a N B)
  exact hα ▸ E

/-- The actual normal-order chart on the SAME M, not a parallel model. -/
@[expose] def chart : Spec (CommRingCat.of C) ⟶ M.scheme :=
  (canonicalData c t w D).chart ≫ (OriginalNormalModelCanonicalIso318.iso c t w D M).hom
instance chart_open : IsOpenImmersion (chart c t w D M) := by
  letI := (canonicalData c t w D).isOpen
  unfold chart
  infer_instance

@[reassoc] theorem source :
    Spec.map (CommRingCat.ofHom
      (IntegralFourRootNormalizationConductor318.normalOrder R a D.coefficients).val.toRingHom) ≫
      chart c t w D M=M.source := by
  unfold chart
  rw [←Category.assoc,(canonicalData c t w D).source]
  exact OriginalNormalModelCanonicalIso318.source c t w D M

@[reassoc] theorem base : chart c t w D M ≫ M.projection=
    Spec.map (CommRingCat.ofHom (algebraMap R[X] C)) ≫ JLineAtlas318.chart R 1 := by
  unfold chart
  rw [Category.assoc,OriginalNormalModelCanonicalIso318.base]
  exact (canonicalData c t w D).base

/-- Keep the exact structural scalar as a composite of ring maps;
no unverified auxiliary algebra structure on the normal order is chosen. -/
@[expose] def scalar : R →+* C := (algebraMap R[X] C).comp Polynomial.C

@[reassoc] theorem structure : chart c t w D M ≫ M.structureMap=
    Spec.map (CommRingCat.ofHom (scalar c t w D)) := by
  change chart c t w D M ≫ M.projection ≫ ProjectiveJLine318.structureMap R=_
  rw [←Category.assoc,base,Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
  rfl
end OriginalNormalOrderChart318
