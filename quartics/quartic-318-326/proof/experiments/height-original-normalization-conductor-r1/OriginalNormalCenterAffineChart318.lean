module
public import AffineSectionCotangentImage318
public section
noncomputable section
namespace OriginalNormalCenterAffineChart318
open NumberField CategoryTheory AlgebraicGeometry
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318 LocalSectionAffineChart318
set_option maxHeartbeats 1000000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)

/-- An actual integral affine chart around the original closed center.
All original proper normal scheme and signed-point data remain fixed. -/
theorem exists_chart : Nonempty (LocalSectionAffineChart318.Data M.structureMap M.center) := by
  letI := M.proper
  exact LocalSectionAffineChart318.exists_data M.structureMap M.center M.center_base

@[expose] def chart : LocalSectionAffineChart318.Data M.structureMap M.center :=
  Classical.choice (exists_chart c t w D M)

/-- The chart's whole generic ring point is the original normalized
source point as a scheme morphism, not just the same projective coordinate.
M.field_roots and original_signed_root retain all four original signs. -/
theorem original_generic :
    Spec.map (CommRingCat.ofHom
      ((algebraMap (V c t w) (K c t)).comp (chart c t w D M).evaluation.hom)) ≫
        (chart c t w D M).inclusion =
      Spec.map (CommRingCat.ofHom M.fieldPoint) ≫ M.source := by
  rw [LocalSectionAffineChart318.Data.generic_section]
  exact M.center_generic

/-- No place, twist normalization or original point is an extra input:
the preceding original producer supplies its actual normal model and center,
then the whole section's affine chart is constructed internally. -/
theorem exists_original_chart
    (hn : ∀ i, RationalContactPoint318.parameters c t i≠0) :
    ∃ (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D),
      Nonempty (LocalSectionAffineChart318.Data M.structureMap M.center) := by
  obtain ⟨D,⟨M⟩⟩ := exists_original_realization c t w hn
  exact ⟨D,M,exists_chart c t w D M⟩

/-- A finite module actually pulled from the relative cotangent module
of the same normal arithmetic model, at its original integral center. -/
abbrev Cotangent := AffineSectionCotangentImage318.Cotangent (chart c t w D M)
abbrev GenericCotangent := AffineSectionCotangentImage318.GenericCotangent
  (chart c t w D M) (K c t)
abbrev integralImage := AffineSectionCotangentImage318.integralImage
  (chart c t w D M) (K c t)

/-- A constructed finite free image spanning the actual generic
cotangent specialization at EVERY finite place, including 2,3,5,7.
This does not identify it with the relative dualizing or Hodge lattice. -/
theorem cotangent_image_properties :
    Module.Finite (V c t w) (Cotangent c t w D M) ∧
    Module.Finite (V c t w) (integralImage c t w D M) ∧
    Module.Free (V c t w) (integralImage c t w D M) ∧
    Submodule.span (K c t) (Set.range (AffineSectionCotangentImage318.toGeneric
      (chart c t w D M) (K c t)))=⊤ :=
  ⟨inferInstance,inferInstance,
    AffineSectionCotangentImage318.image_free (chart c t w D M) (K c t),
    AffineSectionCotangentImage318.image_spans (chart c t w D M) (K c t)⟩
end OriginalNormalCenterAffineChart318
