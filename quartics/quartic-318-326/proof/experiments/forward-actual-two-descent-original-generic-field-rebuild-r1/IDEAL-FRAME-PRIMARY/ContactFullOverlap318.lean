module
public import ContactOverlapMaps318
public import JLineOverlapOpen318
public section
noncomputable section
namespace ContactFullOverlap318
open CategoryTheory AlgebraicGeometry
open ContactOverlapMaps318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance originalOpen : IsOpenImmersion (ContactProjectiveModel318.sourceOpen c):=
  ContactProjectiveModel318.sourceOpen_open c
local instance infinitySourceAlgebra : Algebra (Infinity c) (Source c):=(InfinityOverlapLocalization318.toOpen c).toAlgebra
local instance infinityLocalization : IsLocalization.Away (InfinityOverlapLocalization318.coordinate c) (Source c):=
  SourceInfinityOverlap318.whole_localization c

theorem infinityInclusion_range : (infinityInclusion c).opensRange=
    PrimeSpectrum.basicOpen (InfinityOverlapLocalization318.coordinate c):=by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Source c) (InfinityOverlapLocalization318.coordinate c)

lemma basicOpen_unit {A:Type*} [CommRing A] (x:A) (hx:IsUnit x):
    PrimeSpectrum.basicOpen x=⊤:=by
  ext p
  change (x∉p.asIdeal)↔True
  constructor
  · intro _
    trivial
  · intro _ h
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h hx)

/-- On the entire actual infinity neighborhood, the finite t-chart is exactly
D(u), including every geometric point, not only generic points. -/
theorem infinity_preimage_source :
    InfinityGlobalScheme318.chartEmbedding c⁻¹ᵁ(SourceGlobalAffine318.chartEmbedding c).opensRange=
      PrimeSpectrum.basicOpen (InfinityOverlapLocalization318.coordinate c):=by
  rw [SourceGlobalAffine318.chartEmbedding_range]
  change InfinityGlobalScheme318.chartEmbedding c⁻¹ᵁ
    ((ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ(JLineAtlas318.chart ℚ 1 ''ᵁ ⊤))=_
  rw [←Scheme.Hom.comp_preimage,InfinityStructureMap318.chartEmbedding_over_contact_line]
  unfold ReciprocalInfinityNormalization318.structureMap InfinityGlobalBase318.baseOpen
  rw [Scheme.Hom.comp_preimage,Scheme.Hom.comp_preimage,JLineOverlapOpen318.chart_zero_preimage_one]
  change PrimeSpectrum.basicOpen (ReciprocalInfinityBase318.chartMap c
    (algebraMap (Polynomial ℚ) (ReciprocalInfinityBase318.ReciprocalOpen c) Polynomial.X))=_
  rw [show ReciprocalInfinityBase318.chartMap c
      (algebraMap (Polynomial ℚ) (ReciprocalInfinityBase318.ReciprocalOpen c) Polynomial.X)=
        algebraMap ℚ (Infinity c) (↑((c 0)⁻¹):ℚ)*(InfinityOverlapLocalization318.coordinate c)^2
      from InfinityOverlapLocalization318.reciprocal_coordinate c,
    PrimeSpectrum.basicOpen_mul,PrimeSpectrum.basicOpen_pow _ 2 (by decide),
    basicOpen_unit _ (((c 0)⁻¹).isUnit.map (algebraMap ℚ (Infinity c))),top_inf_eq]

/-- Exact full intersection of the actual finite and infinity chart images
in the actual global contact normalization. -/
theorem actual_full_intersection :
    (SourceGlobalAffine318.chartEmbedding c).opensRange⊓
      (InfinityGlobalScheme318.chartEmbedding c).opensRange=
    (ContactProjectiveModel318.sourceOpen c).opensRange:=by
  rw [inf_comm,←Scheme.Hom.image_preimage_eq_opensRange_inf,
    infinity_preimage_source,←infinityInclusion_range,←Scheme.Hom.opensRange_comp]
  simp only [infinity_square]
/-- The original entire unbranched affine source is the categorical pullback
of the two actual global chart embeddings, with the specified maps. -/
theorem actual_pullback : IsPullback (sourceInclusion c) (infinityInclusion c)
    (SourceGlobalAffine318.chartEmbedding c) (InfinityGlobalScheme318.chartEmbedding c):=by
  apply IsOpenImmersion.isPullback
  · exact (ContactOverlapMaps318.maps_agree c).symm
  · rw [infinity_preimage_source,infinityInclusion_range]
end ContactFullOverlap318
