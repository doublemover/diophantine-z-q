module
public import RefinedSchemeBoundary318
public import WeierstrassBoundaryClass318
public import OriginalCharacterPullbackLines318
public import CompletedCharacterOverlap318

public section
noncomputable section
namespace OriginalCharacterClassPullbacks318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CubicInverseCoordinates318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField : Field (InfinityFieldCoordinates318.L units) :=
  (KummerTensorField318.source_raw_field units).toField
local instance originalOpen : IsOpenImmersion (ContactProjectiveModel318.sourceOpen units) :=
  ContactProjectiveModel318.sourceOpen_open units

/-- The chosen full source finite chart is a refinement, not a claimed full inverse image. -/
theorem finite_refinement (i : Fin 4) : ActualSourceHOnePresentation318.finiteOpen ≤
    completedMap i ⁻¹ᵁ WeierstrassBoundaryClass318.finiteOpen (publishedA i) (publishedB i) := by
  have hs : SourceGlobalAffine318.chartEmbedding units ≫ completedMap i =
      SourceCharacterAffine318.publishedMap i ≫
        WeierstrassGluing318.finiteChart (publishedA i) (publishedB i) := on_finite i
  have hh := AffineChartPullbackScalars318.image_le (completedMap i)
    (SourceGlobalAffine318.chartEmbedding units)
    (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
    (SourceCharacterAffine318.publishedMap i) hs
  simpa only [Scheme.Hom.image_top_eq_opensRange] using hh

theorem infinity_refinement (i : Fin 4) : ActualSourceHOnePresentation318.infinityOpen ≤
    completedMap i ⁻¹ᵁ WeierstrassBoundaryClass318.infinityOpen (publishedA i) (publishedB i) := by
  have hs : InfinityGlobalScheme318.chartEmbedding units ≫ completedMap i =
      Spec.map (CommRingCat.ofHom (CompletedCharacterInfinity318.infinityMap i).toRingHom) ≫
        WeierstrassGluing318.infinityChart (publishedA i) (publishedB i) := on_infinity i
  have hh := AffineChartPullbackScalars318.image_le (completedMap i)
    (InfinityGlobalScheme318.chartEmbedding units)
    (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i))
    (Spec.map (CommRingCat.ofHom (CompletedCharacterInfinity318.infinityMap i).toRingHom)) hs
  simpa only [Scheme.Hom.image_top_eq_opensRange] using hh

@[expose] def overlapHom (i : Fin 4) :
    WeierstrassBoundaryClass318.Overlap (publishedA i) (publishedB i) →ₐ[ℚ]
      ActualSourceHOneCoordinates318.OverlapRing :=
  (CompletedCharacterOverlap318.overlapMap i).comp
    (WeierstrassOverlap318.overlapEquiv (publishedA i) (publishedB i)).toAlgHom

/-- The actual common-open square for the original completed quotient. -/
theorem overlap_square (i : Fin 4) :
    ContactProjectiveModel318.sourceOpen units ≫ completedMap i =
      Spec.map (CommRingCat.ofHom (overlapHom i).toRingHom) ≫
        WeierstrassBoundaryClass318.overlapEmbedding (publishedA i) (publishedB i) := by
  rw [← ContactOverlapMaps318.source_square,Category.assoc,on_finite,
    CompletedCharacterSchemeMaps318.source_restriction,
    ← CompletedCharacterSchemeMaps318.overlap_finite,Category.assoc]
  rfl

@[expose] def sourceRepresentative (i : Fin 4) : ActualSourceHOneCoordinates318.OverlapRing :=
  overlapHom i (WeierstrassBoundaryClass318.representative (publishedA i) (publishedB i))

/-- The specified target overlap class pulls back to its literal original source-ring representative. -/
theorem pullback_class (i : Fin 4) :
    ActualSourceHOnePullbacks318.characterPullback i
      (WeierstrassBoundaryClass318.cohomologyClass (publishedA i) (publishedB i)) =
      ActualSourceHOneCoordinates318.boundary (sourceRepresentative i) := by
  change SchemeSourceCohomology318.pullback (completedMap i) 1
    (MayerVietorisSectionKernel318.sectionBoundary (StructureAdditiveSheaf318.sheaf (Target i))
      _ _ (WeierstrassBoundaryClass318.cover (publishedA i) (publishedB i))
      (WeierstrassBoundaryClass318.overlapSections (publishedA i) (publishedB i)
        (WeierstrassBoundaryClass318.representative (publishedA i) (publishedB i)))) = _
  rw [RefinedSchemeBoundary318.pullback_boundary (completedMap i) _ _ _
    ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
    ActualSourceHOnePresentation318.cover (finite_refinement i) (infinity_refinement i)]
  have hh := RefinedSchemeBoundary318.affine_coordinates (completedMap i)
    (ContactProjectiveModel318.sourceOpen units)
    (WeierstrassBoundaryClass318.overlapEmbedding (publishedA i) (publishedB i))
    (overlapHom i).toRingHom (overlap_square i)
    (WeierstrassBoundaryClass318.finiteOpen (publishedA i) (publishedB i) ⊓
      WeierstrassBoundaryClass318.infinityOpen (publishedA i) (publishedB i))
    (ActualSourceHOnePresentation318.finiteOpen ⊓ ActualSourceHOnePresentation318.infinityOpen)
    (WeierstrassBoundaryClass318.overlap_image (publishedA i) (publishedB i))
    ActualSourceHOneCoordinates318.overlap_image (inf_le_inf (finite_refinement i) (infinity_refinement i))
    (WeierstrassBoundaryClass318.representative (publishedA i) (publishedB i))
  change (completedMap i).appLE _ _ _
      (WeierstrassBoundaryClass318.overlapSections (publishedA i) (publishedB i)
        (WeierstrassBoundaryClass318.representative (publishedA i) (publishedB i))) =
    ActualSourceHOneCoordinates318.overlapSections (sourceRepresentative i) at hh
  rw [hh]
  rfl

/-- Its field image is computed only after the actual source-ring representative has been fixed. -/
theorem sourceRepresentative_embedding (i : Fin 4) :
    SourceOpenFractionField318.openEmbedding units (sourceRepresentative i) =
      CompletedCharacterInfinity318.rawX i ^ 2 / CompletedCharacterInfinity318.rawY i := by
  change SourceOpenFractionField318.openEmbedding units
    (CompletedCharacterOverlap318.overlapMap i
      ((WeierstrassOverlap318.overlapEquiv (publishedA i) (publishedB i))
        ((WeierstrassOverlap318.overlapEquiv (publishedA i) (publishedB i)).symm _))) = _
  rw [AlgEquiv.apply_symm_apply]
  simp only [map_mul,map_pow,WeierstrassOverlap318.ax,
    CompletedCharacterOverlap318.overlapMap_on_finite,CompletedCharacterOverlap318.finiteMap_embedding,
    CompletedCharacterOverlap318.inverse_embedding,div_eq_mul_inv]
  all_goals rfl

/-- The exact original scaling factors and centroid remain in the concrete pullback formula. -/
theorem sourceRepresentative_formula (i : Fin 4) :
    SourceOpenFractionField318.openEmbedding units (sourceRepresentative i) =
      (algebraMap ℚ (InfinityFieldCoordinates318.L units) (xScale i : ℚ) *
        (InfinityFieldCoordinates318.t units - algebraMap ℚ _ (centroid i))) ^ 2 /
      (algebraMap ℚ _ (yScale i : ℚ) *
        CharacterRoot318.root (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i)) := by
  rw [sourceRepresentative_embedding,CompletedCharacterInfinity318.rawX_formula,
    CompletedCharacterInfinity318.rawY_formula]

end OriginalCharacterClassPullbacks318
