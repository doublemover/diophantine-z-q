module
public import VaryingWordGlobalFiniteFlat318
public section
noncomputable section
namespace VaryingWordParameterStructure318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "N" w => VaryingNormalizedWordParameter318.ring R A ι w
local notation "H" w v => VaryingNormalizedWordOverlap318.ring R A ι w v
local notation "inc" => VaryingNormalizedOverlapScheme318.into R A ι
local notation "t" => VaryingNormalizedOverlapScheme318.transition R A ι
local notation "q" => VaryingNormalizedOverlapScheme318.projection R A ι
abbrev chart (w : ι → List A) : VaryingNormalizedOverlapScheme318.chart R A ι w ⟶ Spec (CommRingCat.of R) :=
  VaryingSourceCoefficientPullback318.base R (N w)
@[reassoc] lemma overlap_chart (w v : ι → List A) : inc w v ≫ chart R A ι w=q w v :=
  VaryingSourceCoefficientPullback318.coefficient_base R (N w) (H w v)
    (VaryingNormalizedWordOverlap318.inclusion R A ι w v)

/-- The glued parameter retains its actual coefficient-ring structure. -/
@[expose] def structureMap : VaryingWordChartGluing318.scheme R A ι ⟶ Spec (CommRingCat.of R) := by
  fapply Multicoequalizer.desc
  · exact chart R A ι
  rintro ⟨w,v⟩
  change inc w v ≫ chart R A ι w=(t w v ≫ inc v w) ≫ chart R A ι v
  simp only [Category.assoc,overlap_chart,VaryingNormalizedOverlapScheme318.transition_over_base]
@[reassoc] lemma into_structureMap (w : ι → List A) :
    VaryingWordChartGluing318.into R A ι w ≫ structureMap R A ι=chart R A ι w :=
  Multicoequalizer.π_desc _ _ _ _ _
end VaryingWordParameterStructure318
