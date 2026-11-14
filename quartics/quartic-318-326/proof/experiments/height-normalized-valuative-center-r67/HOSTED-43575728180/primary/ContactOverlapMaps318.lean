module
public import NormalizationSourceCompatibility318
public import SourceInfinityOverlap318
public import SourceGlobalAffine318
public import InfinityStructureMap318
public section
noncomputable section
namespace ContactOverlapMaps318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
abbrev R:=ContactKummerOrder318.R
abbrev Whole:=ContactKummerOrder318.SourceOrder c
abbrev Source:=ContactKummerOrder318.OpenOrder c
abbrev Infinity:=InfinityOpenChart318.OpenOrder c
local instance finiteAlgebra : Algebra R (Source c):=(ContactGlobalProper318.finitePolynomial c).toAlgebra
local instance sourceAlgebra : Algebra (Whole c) (Source c):=(SourceOpenFractionField318.orderToOpen c).toAlgebra
local instance sourceLocalization : IsLocalization.Away (SourceOpenFractionField318.d c) (Source c):=
  SourceOpenFractionField318.open_isLocalization c
local instance infinitySourceAlgebra : Algebra (Infinity c) (Source c):=(InfinityOverlapLocalization318.toOpen c).toAlgebra
local instance infinityLocalization : IsLocalization.Away (InfinityOverlapLocalization318.coordinate c) (Source c):=
  SourceInfinityOverlap318.whole_localization c

@[expose] def sourceInclusion : ContactKummerCover318.cover c⟶Spec (CommRingCat.of (Whole c)):=
  Spec.map (CommRingCat.ofHom (SourceOpenFractionField318.orderToOpen c))
@[expose] def infinityInclusion : ContactKummerCover318.cover c⟶ReciprocalInfinityNormalization318.neighborhood c:=
  Spec.map (CommRingCat.ofHom (InfinityOverlapLocalization318.toOpen c))
instance sourceInclusion_open : IsOpenImmersion (sourceInclusion c):=
  IsOpenImmersion.of_isLocalization (SourceOpenFractionField318.d c)
instance infinityInclusion_open : IsOpenImmersion (infinityInclusion c):=
  IsOpenImmersion.of_isLocalization (InfinityOverlapLocalization318.coordinate c)

theorem sourceClosure_back :
    (integralClosure R (Source c)).val.toRingHom.comp
      (SourceClosureComparison318.sourceClosureEquiv c (SourceGlobalAffine318.source_integrallyClosed c)).symm.toRingHom=
    SourceOpenFractionField318.orderToOpen c:=by
  apply RingHom.ext
  intro x
  apply SourceOpenFractionField318.openEmbedding_injective c
  change SourceOpenFractionField318.openEmbedding c
    (↑((SourceClosureComparison318.sourceClosureEquiv c (SourceGlobalAffine318.source_integrallyClosed c)).symm x))=_
  rw [SourceOpenFractionField318.openEmbedding_on_order]
  have h:=SourceClosureComparison318.sourceClosureEquiv_embedding c
    (SourceGlobalAffine318.source_integrallyClosed c)
    ((SourceClosureComparison318.sourceClosureEquiv c (SourceGlobalAffine318.source_integrallyClosed c)).symm x)
  simpa only [AlgEquiv.apply_symm_apply] using h.symm

/-- The specified full unbranched localization enters the actual global
normalization through its actual finite chart by the original source morphism. -/
theorem source_square : sourceInclusion c≫SourceGlobalAffine318.chartEmbedding c=
    ContactProjectiveModel318.sourceOpen c:=by
  have h:=NormalizationSourceCompatibility318.factored_chart_original (C:=CommRingCat.of (Whole c))
    (CommRingCat.ofHom (ContactGlobalProper318.finitePolynomial c)) (JLineAtlas318.chart ℚ 1)
    (ContactProjectiveModel318.coverMap c) (ContactGlobalProper318.finite_factor c)
    (SourceClosureComparison318.sourceClosureEquiv c (SourceGlobalAffine318.source_integrallyClosed c))
  rw [sourceClosure_back] at h
  exact h

local instance reciprocalSourceAlgebra : Algebra (InfinityGlobalBase318.A c) (Source c):=
  (InfinityGlobalBase318.sourceHom c).toAlgebra
local instance reciprocalInfinityAlgebra : Algebra (InfinityGlobalBase318.A c) (Infinity c):=
  (ReciprocalInfinityBase318.chartMap c).toAlgebra

/-- The actual infinity inclusion gives the same original global source
morphism; its field comparison is not substituted for this Scheme equality. -/
theorem infinity_square : infinityInclusion c≫InfinityGlobalScheme318.chartEmbedding c=
    ContactProjectiveModel318.sourceOpen c:=by
  exact NormalizationSourceCompatibility318.factored_chart_original (C:=CommRingCat.of (Infinity c))
    (CommRingCat.ofHom (InfinityGlobalBase318.sourceHom c)) (InfinityGlobalBase318.baseOpen c)
    (ContactProjectiveModel318.coverMap c) (InfinityGlobalBase318.factorization c)
    (InfinityGlobalChart318.sourceClosureEquiv c)

theorem maps_agree : sourceInclusion c≫SourceGlobalAffine318.chartEmbedding c=
    infinityInclusion c≫InfinityGlobalScheme318.chartEmbedding c:=by
  rw [source_square,infinity_square]
end ContactOverlapMaps318
