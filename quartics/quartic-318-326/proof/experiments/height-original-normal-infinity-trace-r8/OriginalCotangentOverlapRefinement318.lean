module
public import OriginalNormalOrderIntegralComparison318
public import OriginalNormalOrderCotangentCoordinate318
public section
noncomputable section
namespace OriginalCotangentOverlapRefinement318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)
abbrev oldChart := OriginalNormalCenterAffineChart318.chart c t w D M
abbrev orderChart := OriginalNormalOrderSameCenter318.sectionChart c t w D M ht
abbrev integralCommon := OriginalNormalOrderIntegralComparison318.common c t w D M ht
abbrev sourceCommon := OriginalNormalCenterCommonChart318.common c t w D M
abbrev A := (oldChart c t w D M).ring
abbrev C := (orderChart c t w D M ht).ring
abbrev B := SourceOpenRing c t w D
abbrev E := (integralCommon c t w D M ht).ring
abbrev F := (sourceCommon c t w D M).ring

@[expose] def integralInclusion : Spec (E c t w D M ht) ⟶ M.scheme :=
  Spec.map (integralCommon c t w D M ht).left ≫ (oldChart c t w D M).inclusion
@[expose] def sourceInclusion : Spec (F c t w D M) ⟶ M.scheme :=
  Spec.map (sourceCommon c t w D M).left ≫ (oldChart c t w D M).inclusion
@[expose] def integralPoint : E c t w D M ht ⟶ CommRingCat.of (K c t) :=
  (integralCommon c t w D M ht).evaluation ≫ CommRingCat.ofHom (algebraMap (V c t w) (K c t))

lemma integral_point : Spec.map (integralPoint c t w D M ht) ≫
    integralInclusion c t w D M ht =
    Spec.map (CommRingCat.ofHom (algebraMap (V c t w) (K c t))) ≫ M.center := by
  have hp : (integralCommon c t w D M ht).left ≫ integralPoint c t w D M ht =
      (oldChart c t w D M).evaluation ≫
        CommRingCat.ofHom (algebraMap (V c t w) (K c t)) := by
    rw [integralPoint,←Category.assoc,(integralCommon c t w D M ht).left_point]
  calc
    _ = Spec.map ((integralCommon c t w D M ht).left ≫ integralPoint c t w D M ht) ≫
        (oldChart c t w D M).inclusion := by
      rw [Spec.map_comp]
      exact (Category.assoc _ _ _).symm
    _ = Spec.map ((oldChart c t w D M).evaluation ≫
        CommRingCat.ofHom (algebraMap (V c t w) (K c t))) ≫
        (oldChart c t w D M).inclusion := by rw [hp]
    _ = _ := by rw [Spec.map_comp,Category.assoc,(oldChart c t w D M).section_eq]

lemma source_point : Spec.map (sourceCommon c t w D M).evaluation ≫
    sourceInclusion c t w D M =
    Spec.map (CommRingCat.ofHom (algebraMap (V c t w) (K c t))) ≫ M.center := by
  rw [sourceInclusion,←Category.assoc,←Spec.map_comp,
    (sourceCommon c t w D M).left_point]
  exact LocalSectionAffineChart318.Data.generic_section (oldChart c t w D M) _

/-- Refine the two ACTUAL old comparison neighborhoods at the SAME
original signed field point. No new source/model isomorphism is chosen. -/
theorem exists_refinement : Nonempty (ActualCommonAffinePoint318.Data
    (integralInclusion c t w D M ht) (sourceInclusion c t w D M)
    (integralPoint c t w D M ht) (sourceCommon c t w D M).evaluation) := by
  letI := (oldChart c t w D M).openImmersion
  letI := (integralCommon c t w D M ht).left_open
  letI := (sourceCommon c t w D M).left_open
  letI : IsOpenImmersion (integralInclusion c t w D M ht) := inferInstanceAs
    (IsOpenImmersion (Spec.map (integralCommon c t w D M ht).left ≫
      (oldChart c t w D M).inclusion))
  letI : IsOpenImmersion (sourceInclusion c t w D M) := inferInstanceAs
    (IsOpenImmersion (Spec.map (sourceCommon c t w D M).left ≫
      (oldChart c t w D M).inclusion))
  exact ActualCommonAffinePoint318.exists_data _ _ _ _
    ((integral_point c t w D M ht).trans (source_point c t w D M).symm)

@[expose] def refinement := Classical.choice (exists_refinement c t w D M ht)
abbrev G := (refinement c t w D M ht).ring

/-- The two whole ring maps from the old chart agree on the actual
refinement, by its scheme square and the original open-chart monomorphism. -/
lemma old_square :
    (integralCommon c t w D M ht).left ≫ (refinement c t w D M ht).left =
      (sourceCommon c t w D M).left ≫ (refinement c t w D M ht).right := by
  letI := (oldChart c t w D M).openImmersion
  apply Spec.map_injective
  apply (cancel_mono (oldChart c t w D M).inclusion).mp
  rw [Spec.map_comp,Spec.map_comp,Category.assoc,Category.assoc]
  exact (refinement c t w D M ht).square

@[expose] def orderToSource : C c t w D M ht ⟶ CommRingCat.of (B c t w D) :=
  CommRingCat.ofHom (IntegralFourRootNormalizationConductor318.normalOrder
    (V c t w) (contacts c t w) D.coefficients).val.toRingHom

/-- The normal-order route through the integral overlap and its route
through the original source agree as WHOLE ring maps on the refinement. -/
lemma order_square :
    (integralCommon c t w D M ht).right ≫ (refinement c t w D M ht).left =
      orderToSource c t w D M ht ≫ (sourceCommon c t w D M).right ≫
        (refinement c t w D M ht).right := by
  letI := (orderChart c t w D M ht).openImmersion
  apply Spec.map_injective
  apply (cancel_mono (orderChart c t w D M ht).inclusion).mp
  simp only [Spec.map_comp,Category.assoc]
  rw [show Spec.map (orderToSource c t w D M ht) ≫
      (orderChart c t w D M ht).inclusion=M.source from
    OriginalNormalOrderChart318.source c t w D M]
  rw [←(sourceCommon c t w D M).square,
    ←(integralCommon c t w D M ht).square]
  exact (refinement c t w D M ht).square
end OriginalCotangentOverlapRefinement318
