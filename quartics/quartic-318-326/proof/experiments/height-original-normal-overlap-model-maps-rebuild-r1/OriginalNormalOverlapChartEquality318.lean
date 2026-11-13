module
public import OriginalNormalOverlapChartMaps318
public import AffineDominantSeparatedExt318
public section
noncomputable section
namespace OriginalNormalOverlapChartEquality318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalOverlapChartMaps318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "Oi" => IntegralOriginalNormalOverlap318.InfinityOverlap R a d
local instance sourceDomain : IsDomain B :=
  IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)

/-- The full reciprocal overlap is reduced because it is an actual
integral-closure subring of the produced source domain. -/
instance overlap_domain : IsDomain Oi := by
  letI := (IntegralOriginalNormalOverlap318.infinityMap R a d).toAlgebra
  infer_instance

instance source_dominant : IsDominant (infinitySource c t w D) :=
  AffineDominantSeparatedExt318.dominant
    (IntegralClosureAlongRingMap318.inclusion (IntegralOriginalNormalOverlap318.infinityMap R a d))
    Subtype.val_injective

/-- Equality of the actual whole overlap-chart maps into the SAME M.
This uses density of the entire source and actual properness of M over R. -/
@[reassoc] theorem square : NormalOverlapReciprocalDualSheaf318.map R a d ≫
    finite c t w D M=infinity c t w D M := by
  letI : IsProper M.structureMap := M.proper
  apply AffineDominantSeparatedExt318.ext_over_affine
    (CommRingCat.of R) M.structureMap (infinitySource c t w D)
  rw [←Category.assoc,source_square,finite_source,infinity_source]

/-- Preserve the literal original field-valued point through the chart
equality; neither its signs nor its source are chosen anew. -/
@[reassoc] lemma signed_point :
    Spec.map (CommRingCat.ofHom M.fieldPoint) ≫ infinitySource c t w D ≫
      NormalOverlapReciprocalDualSheaf318.map R a d ≫ finite c t w D M=
        Spec.map (CommRingCat.ofHom M.fieldPoint) ≫ M.source := by
  rw [square,infinity_source]
end OriginalNormalOverlapChartEquality318
