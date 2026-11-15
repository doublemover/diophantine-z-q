module
public import AffineHOnePointedNaturality318
public import CompletedCharacterSchemeMaps318
public import FifthCompletedFinite318
public section
noncomputable section
namespace OriginalFiveHOnePointedNaturality318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open ContactRelativeLinePresheaf318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral : IsIntegral ActualSourceHOnePresentation318.Source :=
  ContactProjectiveModel318.model_integral units
local instance characterIntegral (a : Fin 4) : IsIntegral (CompletedCharacterSchemeMaps318.Target a) :=
  (CompletedCharacterProper318.target_proper_integral a).2
local instance fifthIntegral : IsIntegral FifthCompletedGlobal318.Target := FifthCompletedProper318.target_proper_integral.2
local instance fifthFinite : IsFinite FifthCompletedGlobal318.map := FifthCompletedFinite318.finite
/-- Original finite-chart factorization, reused with the same full source open. -/
lemma finite_refinement (a : Fin 4) : ActualSourceHOnePresentation318.finiteOpen ≤
    CompletedCharacterGlobal318.completedMap a ⁻¹ᵁ OriginalHOnePointedMaps318.finiteOpen (publishedA a) (publishedB a) := by
  have hh := AffineChartPullbackScalars318.image_le (CompletedCharacterGlobal318.completedMap a)
    (SourceGlobalAffine318.chartEmbedding units) (WeierstrassGluing318.finiteChart (publishedA a) (publishedB a))
    (SourceCharacterAffine318.publishedMap a) (CompletedCharacterGlobal318.on_finite a)
  simpa only [Scheme.Hom.image_top_eq_opensRange] using hh
lemma infinity_refinement (a : Fin 4) : ActualSourceHOnePresentation318.infinityOpen ≤
    CompletedCharacterGlobal318.completedMap a ⁻¹ᵁ OriginalHOnePointedMaps318.infinityOpen (publishedA a) (publishedB a) := by
  have hh := AffineChartPullbackScalars318.image_le (CompletedCharacterGlobal318.completedMap a)
    (InfinityGlobalScheme318.chartEmbedding units) (WeierstrassGluing318.infinityChart (publishedA a) (publishedB a))
    (Spec.map (CommRingCat.ofHom (CompletedCharacterInfinity318.infinityMap a).toRingHom))
    (CompletedCharacterGlobal318.on_infinity a)
  simpa only [Scheme.Hom.image_top_eq_opensRange] using hh
/-- All four ORIGINAL global H1 pullbacks commute with the ACTUAL pointed-line
pullbacks, using the unchanged chosen source and target two-chart maps. -/
lemma character (a : Fin 4)
    (z : SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1) :
    OriginalFivePointedDeformations318.characterPullback a (OriginalHOnePointedMaps318.character a z) =
      OriginalHOnePointedMaps318.source (ActualSourceHOnePullbacks318.characterPullback a z) :=
  AffineHOnePointedNaturality318.naturality sourceStructure (characterStructure a)
    (CompletedCharacterGlobal318.completedMap a) (CompletedCharacterGlobal318.over_Q a)
    (OriginalHOnePointedMaps318.finiteOpen (publishedA a) (publishedB a))
    (OriginalHOnePointedMaps318.infinityOpen (publishedA a) (publishedB a))
    ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart (publishedA a) (publishedB a)))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart (publishedA a) (publishedB a)))
    ActualSourceHOnePresentation318.finite_affine ActualSourceHOnePresentation318.infinity_affine
    (OriginalHOnePointedMaps318.target_cover (publishedA a) (publishedB a)) ActualSourceHOnePresentation318.cover
    (finite_refinement a) (infinity_refinement a) z
abbrev fifthFiniteOpen := OriginalHOnePointedMaps318.finiteOpen FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
abbrev fifthInfinityOpen := OriginalHOnePointedMaps318.infinityOpen FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
lemma fifth_preimage_cover :
    (FifthCompletedGlobal318.map ⁻¹ᵁ fifthFiniteOpen) ⊔ (FifthCompletedGlobal318.map ⁻¹ᵁ fifthInfinityOpen) = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, OriginalHOnePointedMaps318.target_cover, Scheme.Hom.preimage_top]
/-- A genuine source-H1 deformation map using the ORIGINAL fifth quotient's
full inverse-image affine cover. It is NOT silently equated to the canonical
contact finite/infinity-cover construction. -/
@[expose] def sourceForFifth : ActualSourceHOnePullbacks318.SourceHOne → OriginalFivePointedDeformations318.SourceClass :=
  AffineHOnePointedDeformation318.map sourceStructure
    (FifthCompletedGlobal318.map ⁻¹ᵁ fifthFiniteOpen) (FifthCompletedGlobal318.map ⁻¹ᵁ fifthInfinityOpen)
    ((isAffineOpen_opensRange (WeierstrassGluing318.finiteChart
      FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)).preimage FifthCompletedGlobal318.map)
    ((isAffineOpen_opensRange (WeierstrassGluing318.infinityChart
      FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)).preimage FifthCompletedGlobal318.map)
    fifth_preimage_cover
/-- Exact fifth original-map naturality on its genuine adapted source cover.
Common-cover independence is still required to replace sourceForFifth by source. -/
lemma fifth (z : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1) :
    OriginalFivePointedDeformations318.fifthPullback (OriginalHOnePointedMaps318.fifth z) =
      sourceForFifth (ActualSourceHOnePullbacks318.fifthPullback z) :=
  AffineHOnePointedNaturality318.naturality sourceStructure fifthStructure
    FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q
    fifthFiniteOpen fifthInfinityOpen
    (FifthCompletedGlobal318.map ⁻¹ᵁ fifthFiniteOpen) (FifthCompletedGlobal318.map ⁻¹ᵁ fifthInfinityOpen)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B))
    ((isAffineOpen_opensRange (WeierstrassGluing318.finiteChart FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)).preimage FifthCompletedGlobal318.map)
    ((isAffineOpen_opensRange (WeierstrassGluing318.infinityChart FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)).preimage FifthCompletedGlobal318.map)
    (OriginalHOnePointedMaps318.target_cover FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)
    fifth_preimage_cover le_rfl le_rfl z
end OriginalFiveHOnePointedNaturality318
