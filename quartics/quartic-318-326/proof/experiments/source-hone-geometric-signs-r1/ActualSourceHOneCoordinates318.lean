module
public import ActualSourceHOneQuotient318
public import AffineChartRingSections318
public import ContactFullOverlap318

public section
noncomputable section
namespace ActualSourceHOneCoordinates318
open AlgebraicGeometry CategoryTheory Opposite
open ActualSourceHOnePresentation318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev units := SourceTwistArithmetic318.units
abbrev FiniteRing := ContactKummerOrder318.SourceOrder units
abbrev InfinityRing := InfinityOpenChart318.OpenOrder units
abbrev OverlapRing := ContactKummerOrder318.OpenOrder units

local instance sourceIntegral : IsIntegral Source := ContactProjectiveModel318.model_integral units
local instance commonOpen : IsOpenImmersion (ContactProjectiveModel318.sourceOpen units) :=
  ContactProjectiveModel318.sourceOpen_open units

@[expose] def finiteSections : FiniteRing ≃+ Γ(Source,finiteOpen) :=
  AffineChartRingSections318.equivalence (SourceGlobalAffine318.chartEmbedding units)

@[expose] def infinitySections : InfinityRing ≃+ Γ(Source,infinityOpen) :=
  AffineChartRingSections318.equivalence (InfinityGlobalScheme318.chartEmbedding units)

@[expose] def overlapSections : OverlapRing ≃+ Γ(Source,finiteOpen ⊓ infinityOpen) :=
  AffineChartRingSections318.equivalenceOn (ContactProjectiveModel318.sourceOpen units)
    (finiteOpen ⊓ infinityOpen) (ContactFullOverlap318.actual_full_intersection units).symm

@[expose] def finiteMap : FiniteRing →+* OverlapRing := SourceOpenFractionField318.orderToOpen units
@[expose] def infinityMap : InfinityRing →+* OverlapRing := InfinityOverlapLocalization318.toOpen units

/-- Literal finite-chart algebra localization agrees with the original ring-section restriction. -/
theorem finite_restriction (a : FiniteRing) :
    Source.presheaf.map (homOfLE inf_le_left : finiteOpen ⊓ infinityOpen ⟶ finiteOpen).op
      (finiteSections a) = overlapSections (finiteMap a) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom finiteMap)) :=
    ContactOverlapMaps318.sourceInclusion_open units
  exact AffineChartRingSections318.restrict_to_on
    (SourceGlobalAffine318.chartEmbedding units) finiteMap
    (ContactProjectiveModel318.sourceOpen units) (ContactOverlapMaps318.source_square units)
    (finiteOpen ⊓ infinityOpen) (ContactFullOverlap318.actual_full_intersection units).symm
    inf_le_left a

/-- Literal infinity-chart localization agrees on the full actual overlap. -/
theorem infinity_restriction (b : InfinityRing) :
    Source.presheaf.map (homOfLE inf_le_right : finiteOpen ⊓ infinityOpen ⟶ infinityOpen).op
      (infinitySections b) = overlapSections (infinityMap b) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom infinityMap)) :=
    ContactOverlapMaps318.infinityInclusion_open units
  exact AffineChartRingSections318.restrict_to_on
    (InfinityGlobalScheme318.chartEmbedding units) infinityMap
    (ContactProjectiveModel318.sourceOpen units) (ContactOverlapMaps318.infinity_square units)
    (finiteOpen ⊓ infinityOpen) (ContactFullOverlap318.actual_full_intersection units).symm
    inf_le_right b

/-- The original two concrete algebra maps, with the Mayer-Vietoris difference sign. -/
@[expose] def difference : (FiniteRing × InfinityRing) →+ OverlapRing :=
  finiteMap.toAddMonoidHom.comp (AddMonoidHom.fst _ _) -
    infinityMap.toAddMonoidHom.comp (AddMonoidHom.snd _ _)

/-- Concrete overlap-ring coordinates map to genuine whole-source H1. -/
@[expose] def boundary : OverlapRing →+ ActualSourceHOnePullbacks318.SourceHOne :=
  ActualSourceHOnePresentation318.boundary.comp overlapSections.toAddMonoidHom

theorem boundary_apply (x : OverlapRing) :
    boundary x = ActualSourceHOnePresentation318.boundary (overlapSections x) := rfl

theorem boundary_surjective : Function.Surjective boundary :=
  ActualSourceHOnePresentation318.boundary_surjective.comp overlapSections.surjective

/-- No implicit chart-image or generic-stalk replacement remains in the kernel. -/
theorem boundary_eq_zero_iff (x : OverlapRing) :
    boundary x = 0 ↔ ∃ a : FiniteRing, ∃ b : InfinityRing,
      finiteMap a - infinityMap b = x := by
  change ActualSourceHOnePresentation318.boundary (overlapSections x) = 0 ↔ _
  rw [ActualSourceHOneQuotient318.boundary_eq_zero_iff_mem_range]
  change (∃ z : Γ(Source,finiteOpen) × Γ(Source,infinityOpen),
    ActualSourceHOneQuotient318.difference z = overlapSections x) ↔ _
  constructor
  · rintro ⟨⟨a,b⟩,hab⟩
    obtain ⟨a,rfl⟩ := finiteSections.surjective a
    obtain ⟨b,rfl⟩ := infinitySections.surjective b
    refine ⟨a,b,overlapSections.injective ?_⟩
    rw [map_sub, ← finite_restriction, ← infinity_restriction]
    exact hab
  · rintro ⟨a,b,hab⟩
    refine ⟨(finiteSections a,infinitySections b),?_⟩
    change Source.presheaf.map _ (finiteSections a) - Source.presheaf.map _ (infinitySections b) = _
    rw [finite_restriction,infinity_restriction, ← map_sub, hab]

theorem kernel_eq_range : boundary.ker = difference.range := by
  ext x
  change boundary x = 0 ↔ ∃ z : FiniteRing × InfinityRing, difference z = x
  rw [boundary_eq_zero_iff]
  exact ⟨fun ⟨a,b,h⟩ => ⟨(a,b),h⟩,fun ⟨⟨a,b⟩,h⟩ => ⟨a,b,h⟩⟩

/-- Actual H1 as the quotient of the original explicit overlap ring by the
sum of the two original affine-ring images. No dimension claim is used. -/
@[expose] def equivalence : OverlapRing ⧸ difference.range ≃+
    ActualSourceHOnePullbacks318.SourceHOne :=
  (QuotientAddGroup.quotientAddEquivOfEq kernel_eq_range.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective boundary boundary_surjective)

theorem equivalence_mk (x : OverlapRing) :
    equivalence (QuotientAddGroup.mk x) = boundary x := rfl

end ActualSourceHOneCoordinates318
