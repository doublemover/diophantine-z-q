module
public import OriginalNormalReciprocalDualTransition318
public import OriginalNormalOrderChart318
public import OriginalNormalInfinityChart318
public section
noncomputable section
namespace OriginalNormalOverlapChartMaps318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "Of" => IntegralOriginalNormalOverlap318.FiniteOverlap R a d
local notation "Oi" => IntegralOriginalNormalOverlap318.InfinityOverlap R a d
local instance sourceDomain : IsDomain B :=
  IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)

@[expose] def finiteSource : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of Of) :=
  Spec.map (CommRingCat.ofHom
    (IntegralClosureAlongRingMap318.inclusion (IntegralOriginalNormalOverlap318.finiteMap R a d)))
@[expose] def infinitySource : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of Oi) :=
  Spec.map (CommRingCat.ofHom
    (IntegralClosureAlongRingMap318.inclusion (IntegralOriginalNormalOverlap318.infinityMap R a d)))

/-- Both entire localized orders map into the SAME original M. -/
@[expose] def finite : Spec (CommRingCat.of Of) ⟶ M.scheme :=
  IntegralNormalFiniteDualSheafRestriction318.map R a d ≫
    OriginalNormalOrderChart318.chart c t w D M
@[expose] def infinity : Spec (CommRingCat.of Oi) ⟶ M.scheme :=
  IntegralNormalInfinityDualSheafRestriction318.map R a d ≫
    OriginalNormalInfinityChart318.chart c t w D M

instance finite_open : IsOpenImmersion (finite c t w D M) := by
  unfold finite
  infer_instance
instance infinity_open : IsOpenImmersion (infinity c t w D M) := by
  unfold infinity
  infer_instance

@[reassoc] lemma finite_source : finiteSource c t w D ≫ finite c t w D M=M.source := by
  unfold finite finiteSource IntegralNormalFiniteDualSheafRestriction318.map
  rw [←Category.assoc,←Spec.map_comp]
  exact OriginalNormalOrderChart318.source c t w D M

@[reassoc] lemma infinity_source : infinitySource c t w D ≫ infinity c t w D M=M.source := by
  unfold infinity infinitySource IntegralNormalInfinityDualSheafRestriction318.map
  rw [←Category.assoc,←Spec.map_comp]
  exact OriginalNormalInfinityChart318.source c t w D M

/-- The accepted ring equivalence is the identity on ambient source elements,
including every original signed root. This square keeps its exact orientation. -/
@[reassoc] lemma source_square : infinitySource c t w D ≫
    NormalOverlapReciprocalDualSheaf318.map R a d=finiteSource c t w D := by
  unfold infinitySource finiteSource NormalOverlapReciprocalDualSheaf318.map
  rw [←Spec.map_comp]
  rfl
end OriginalNormalOverlapChartMaps318
