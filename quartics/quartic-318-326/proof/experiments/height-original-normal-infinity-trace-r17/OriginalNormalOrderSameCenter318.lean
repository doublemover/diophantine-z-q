module
public import OriginalNormalOrderIntegralPoint318
public import SeparatedValuationCenterEquality318
public section
noncomputable section
namespace OriginalNormalOrderSameCenter318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalOrderChart318 OriginalNormalOrderIntegralPoint318
set_option maxHeartbeats 1200000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)
local notation "R" => V c t w
local notation "C" => Order c t w D
local instance : IsProper M.structureMap := M.proper

lemma over_base :
    (Spec.map (CommRingCat.ofHom (evaluation c t w D M ht)) ≫ chart c t w D M) ≫
      M.structureMap=𝟙 _ := by
  rw [Category.assoc,OriginalNormalOrderChart318.structure,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((evaluation c t w D M ht).comp (scalar c t w D)))=𝟙 _
  rw [retraction]
  simp

/-- The integral evaluation point is exactly the OLD center. The
proof uses both exact signed generic equality and exact base equality,
then separated valuative uniqueness, not a new center choice. -/
theorem same_center :
    Spec.map (CommRingCat.ofHom (evaluation c t w D M ht)) ≫ chart c t w D M=M.center := by
  apply SeparatedValuationCenterEquality318.eq R (K c t) M.structureMap
  · exact (OriginalNormalOrderIntegralPoint318.generic c t w D M ht).trans M.center_generic.symm
  · exact (over_base c t w D M ht).trans M.center_base.symm

/-- This is now an actual affine section chart of the unchanged
center, with literal normal-order scalar and integral evaluation maps. -/
@[expose] def sectionChart : LocalSectionAffineChart318.Data M.structureMap M.center where
  ring := CommRingCat.of C
  inclusion := chart c t w D M
  openImmersion := inferInstance
  scalar := CommRingCat.ofHom (OriginalNormalOrderChart318.scalar c t w D)
  evaluation := CommRingCat.ofHom (OriginalNormalOrderIntegralPoint318.evaluation c t w D M ht)
  over_base := (OriginalNormalOrderChart318.structure c t w D M).symm
  section_eq := same_center c t w D M ht
  retraction := by
    apply CommRingCat.hom_ext
    exact OriginalNormalOrderIntegralPoint318.retraction c t w D M ht
  finite_type := by
    have hft : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (OriginalNormalOrderChart318.scalar c t w D))) := by
      rw [←OriginalNormalOrderChart318.structure c t w D M]
      infer_instance
    exact HasRingHomProperty.Spec_iff.mp hft

/-- The actual finite integral cotangent specialization on the normal
order chart. This is not the relative dualizing or Hodge module. -/
abbrev Cotangent := AffineSectionCotangentImage318.Cotangent (sectionChart c t w D M ht)
abbrev GenericCotangent := AffineSectionCotangentImage318.GenericCotangent
  (sectionChart c t w D M ht) (K c t)
end OriginalNormalOrderSameCenter318
