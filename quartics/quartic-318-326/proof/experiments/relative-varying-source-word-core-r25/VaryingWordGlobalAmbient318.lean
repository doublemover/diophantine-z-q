module
public import VaryingWordGlobalOriginalMap318
public section
noncomputable section
namespace VaryingWordGlobalAmbient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "N" w => VaryingNormalizedWordParameter318.ring R A ι w
local notation "u" => VaryingWordChartGluing318.into R A ι
local notation "p" => VaryingNormalizedUniversalFamily318.projection R A ι
local notation "z" => VaryingWordFamilyGluing318.into R A ι
local notation "b" => VaryingWordParameterStructure318.structureMap R A ι
local notation "a" => VaryingSourceCoefficientPullback318.base R A
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι
local notation "original" => VaryingWordGlobalOriginalMap318.original R A ι
abbrev ambient : Scheme := pullback b a
abbrev projection : ambient R A ι ⟶ VaryingWordChartGluing318.scheme R A ι := pullback.fst b a
@[expose] def into : VaryingWordFamilyGluing318.scheme R A ι ⟶ ambient R A ι :=
  pullback.lift π original (VaryingWordGlobalOriginalMap318.structure_square R A ι).symm
@[reassoc] lemma into_projection : into R A ι ≫ projection R A ι=π := pullback.lift_fst _ _ _
@[reassoc] lemma into_original : into R A ι ≫ pullback.snd b a=original := pullback.lift_snd _ _ _

abbrev chart (w : ι → List A) : Scheme := Spec (CommRingCat.of (N w ⊗[R] A))
local notation "cp" w => VaryingSourceCoefficientPullback318.projection R A (N w)
local notation "co" w => VaryingSourceCoefficientPullback318.original R A (N w)
@[expose] def chartInto (w : ι → List A) : chart R A ι w ⟶ ambient R A ι :=
  pullback.lift (cp w ≫ u w) (co w) (by
    rw [Category.assoc,VaryingWordParameterStructure318.into_structureMap]
    exact (VaryingSourceCoefficientPullback318.tensor_cartesian R A (N w)).w)
@[reassoc] lemma chartInto_projection (w : ι → List A) :
    chartInto R A ι w ≫ projection R A ι=cp w ≫ u w := pullback.lift_fst _ _ _
@[reassoc] lemma chartInto_original (w : ι → List A) :
    chartInto R A ι w ≫ pullback.snd b a=co w := pullback.lift_snd _ _ _

/-- The original tensor source chart is the actual base change of the
global source ambient scheme along the same parameter chart. -/
lemma chart_cartesian (w : ι → List A) : IsPullback (chartInto R A ι w) (cp w)
    (projection R A ι) (u w) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd b a) (h₂₂ := b)
  · simpa only [chartInto_original,VaryingWordParameterStructure318.into_structureMap] using
      (VaryingSourceCoefficientPullback318.tensor_cartesian R A (N w)).flip
  · exact chartInto_projection R A ι w
  · exact (IsPullback.of_hasPullback b a).flip
instance chartInto_open (w : ι → List A) : IsOpenImmersion (chartInto R A ι w) :=
  MorphismProperty.of_isPullback (chart_cartesian R A ι w).flip inferInstance

lemma chart_into (w : ι → List A) :
    VaryingNormalizedUniversalFamily318.intoSource R A ι w ≫ chartInto R A ι w=
      z w ≫ into R A ι := by
  apply pullback.hom_ext
  · simp only [Category.assoc,chartInto_projection,into_projection]
    rw [← Category.assoc,VaryingQuotientCoefficientPullback318.into_projection,
      VaryingWordGlobalFamilyProjection318.into_projection]
  · simp only [Category.assoc,chartInto_original,into_original]
    exact (VaryingWordGlobalOriginalMap318.into_original R A ι w).symm

/-- The original full-ideal closed quotient is recovered by base-changing
the global source map over the actual tensor source chart. -/
lemma quotient_cartesian (w : ι → List A) : IsPullback (z w)
    (VaryingNormalizedUniversalFamily318.intoSource R A ι w) (into R A ι) (chartInto R A ι w) := by
  apply IsPullback.of_bot (v₂₁ := cp w) (v₂₂ := projection R A ι)
  · simpa only [into_projection,VaryingQuotientCoefficientPullback318.into_projection] using
      VaryingWordGlobalFamilyCartesian318.square R A ι w
  · exact (chart_into R A ι w).symm
  · exact chart_cartesian R A ι w
end VaryingWordGlobalAmbient318
