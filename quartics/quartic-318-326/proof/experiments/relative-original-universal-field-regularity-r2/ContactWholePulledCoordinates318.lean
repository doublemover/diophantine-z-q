module
public import ContactOriginalPositiveBaseCoordinates318
public import ContactPulledRatios318
public import RestrictedMapBijective318
public import RestrictionScalarRelation318
public section
noncomputable section
namespace ContactWholePulledCoordinates318
open AlgebraicGeometry CategoryTheory
open ContactOriginalWholeRestriction318 ContactOriginalPositiveBaseCoordinates318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

lemma infinity_square : ContactWholeInfinityScheme318.into c ≫
    ContactBicanonicalProjectiveMap318.projectiveMap c =
    ContactWholeInfinityScheme318.projection c ≫ JLineAtlas318.chart ℚ 0 := by
  rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
  exact ContactWholeInfinityScheme318.over_base c

/-- The original pulled projective coordinate generates on the ENTIRE
finite chart, not merely on its old branch-chart refinement. -/
lemma zero_finite_isIso : IsIso
    ((Scheme.Modules.restrictFunctor (SourceGlobalAffine318.chartEmbedding c)).map
      (ContactPulledCoordinates318.zeroMap c)) := by
  letI := ProjectiveLineCoordinateGenerators318.zero_finite_isIso
  exact PulledCoordinateMaps318.restrict_isIso
    (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.zeroMap
    (JLineAtlas318.chart ℚ 1) (SourceGlobalAffine318.chartEmbedding c)
    (ContactBicanonicalDegree318.affineMap c) (ContactBicanonicalDegree318.affine_square c).symm

/-- The reciprocal pulled coordinate generates on the ENTIRE original
infinity polynomial chart, including all previously omitted points. -/
lemma one_infinity_isIso : IsIso
    ((Scheme.Modules.restrictFunctor (ContactWholeInfinityScheme318.into c)).map
      (ContactPulledCoordinates318.oneMap c)) := by
  letI := ProjectiveLineCoordinateGenerators318.one_infinity_isIso
  exact PulledCoordinateMaps318.restrict_isIso
    (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.oneMap
    (JLineAtlas318.chart ℚ 0) (ContactWholeInfinityScheme318.into c)
    (ContactWholeInfinityScheme318.projection c) (infinity_square c)

lemma zero_bijective (V : (X c).Opens) (hV : V ≤ finiteOpen c) :
    Function.Bijective (SectionGeneratedGluing318.genLinear (ContactPulledCoordinates318.zeroMap c) V) := by
  letI := zero_finite_isIso c
  exact RestrictedMapBijective318.bijective (SourceGlobalAffine318.chartEmbedding c)
    (ContactPulledCoordinates318.zeroMap c) V hV

lemma one_bijective (V : (X c).Opens) (hV : V ≤ infinityOpen c) :
    Function.Bijective (SectionGeneratedGluing318.genLinear (ContactPulledCoordinates318.oneMap c) V) := by
  letI := one_infinity_isIso c
  exact RestrictedMapBijective318.bijective (ContactWholeInfinityScheme318.into c)
    (ContactPulledCoordinates318.oneMap c) V hV

/-- The SAME original projective coordinate ratio on the full finite open. -/
lemma finite_relation :
    SectionGeneratedGluing318.genLinear (ContactPulledCoordinates318.oneMap c) (finiteOpen c) 1 =
      finiteCoordinate c •
        SectionGeneratedGluing318.genLinear (ContactPulledCoordinates318.zeroMap c) (finiteOpen c) 1 := by
  have h := PullbackLocalRelations318.relation
    (ContactBicanonicalProjectiveMap318.projectiveMap c) (JLineAtlas318.chart ℚ 1)
    (SourceGlobalAffine318.chartEmbedding c) (ContactBicanonicalDegree318.affineMap c)
    (ContactBicanonicalDegree318.affine_square c).symm
    ProjectiveLineCoordinates318.zeroMap ProjectiveLineCoordinates318.oneMap
    ProjectiveLineCoordinates318.coordinate ProjectiveLineCoordinateRelations318.finite_relation
  exact RestrictionScalarRelation318.top_value (SourceGlobalAffine318.chartEmbedding c)
    (ContactPulledCoordinates318.zeroMap c) (ContactPulledCoordinates318.oneMap c)
    ((ContactBicanonicalDegree318.affineMap c).appTop ProjectiveLineCoordinates318.coordinate) h

/-- The SAME original reciprocal projective ratio on the full infinity open. -/
lemma infinity_relation :
    SectionGeneratedGluing318.genLinear (ContactPulledCoordinates318.zeroMap c) (infinityOpen c) 1 =
      infinityCoordinate c •
        SectionGeneratedGluing318.genLinear (ContactPulledCoordinates318.oneMap c) (infinityOpen c) 1 := by
  have h := PullbackLocalRelations318.relation
    (ContactBicanonicalProjectiveMap318.projectiveMap c) (JLineAtlas318.chart ℚ 0)
    (ContactWholeInfinityScheme318.into c) (ContactWholeInfinityScheme318.projection c)
    (infinity_square c) ProjectiveLineCoordinates318.oneMap ProjectiveLineCoordinates318.zeroMap
    ProjectiveLineCoordinates318.coordinate ProjectiveLineCoordinateRelations318.infinity_relation
  exact RestrictionScalarRelation318.top_value (ContactWholeInfinityScheme318.into c)
    (ContactPulledCoordinates318.oneMap c) (ContactPulledCoordinates318.zeroMap c)
    ((ContactWholeInfinityScheme318.projection c).appTop ProjectiveLineCoordinates318.coordinate) h
end ContactWholePulledCoordinates318
