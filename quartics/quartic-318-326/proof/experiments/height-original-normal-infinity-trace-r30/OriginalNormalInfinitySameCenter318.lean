module
public import OriginalNormalInfinityIntegralPoint318
public section
noncomputable section
namespace OriginalNormalInfinitySameCenter318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalInfinityOrder318 OriginalNormalInfinityIntegralPoint318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t:K c t)⁻¹ ≤ 1)
local notation "R" => V c t w
local notation "C" => Order c t w D

lemma over_base :
    (Spec.map (CommRingCat.ofHom (evaluation c t w D M ht)) ≫
      OriginalNormalInfinityChart318.chart c t w D M) ≫ M.structureMap=𝟙 _ := by
  rw [Category.assoc,OriginalNormalInfinityChart318.structure,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((evaluation c t w D M ht).comp (scalar c t w D)))=𝟙 _
  rw [retraction]
  simp

/-- Reciprocal integrality produces precisely the OLD closed center,
by signed generic equality and separated valuative uniqueness. -/
theorem same_center :
    Spec.map (CommRingCat.ofHom (evaluation c t w D M ht)) ≫
      OriginalNormalInfinityChart318.chart c t w D M=M.center := by
  letI : IsProper M.structureMap := M.proper
  apply SeparatedValuationCenterEquality318.eq R (K c t) M.structureMap
  · exact (OriginalNormalInfinityIntegralPoint318.generic c t w D M ht).trans M.center_generic.symm
  · exact (over_base c t w D M ht).trans M.center_base.symm

/-- An actual integral affine chart of the SAME section at infinity.
It constructs native cotangent specialization without identifying it with
the dualizing module or assuming smoothness of a bad special fiber. -/
@[expose] def sectionChart : LocalSectionAffineChart318.Data M.structureMap M.center := by
  letI : IsProper M.structureMap := M.proper
  exact
    { ring := CommRingCat.of C
      inclusion := OriginalNormalInfinityChart318.chart c t w D M
      openImmersion := inferInstance
      scalar := CommRingCat.ofHom (OriginalNormalInfinityOrder318.scalar c t w D)
      evaluation := CommRingCat.ofHom (evaluation c t w D M ht)
      over_base := (OriginalNormalInfinityChart318.structure c t w D M).symm
      section_eq := same_center c t w D M ht
      retraction := by
        apply CommRingCat.hom_ext
        exact OriginalNormalInfinityIntegralPoint318.retraction c t w D M ht
      finite_type := by
        have hft : LocallyOfFiniteType
            (Spec.map (CommRingCat.ofHom (OriginalNormalInfinityOrder318.scalar c t w D))) := by
          rw [←OriginalNormalInfinityChart318.structure c t w D M]
          infer_instance
        exact HasRingHomProperty.Spec_iff.mp hft }

abbrev Cotangent := AffineSectionCotangentImage318.Cotangent (sectionChart c t w D M ht)
abbrev GenericCotangent := AffineSectionCotangentImage318.GenericCotangent
  (sectionChart c t w D M ht) (K c t)

/-- The actual original coordinate selects at least one of the two
integral branches at EVERY finite place. No good-prime exclusion. -/
lemma coordinate_dichotomy : w (t:K c t) ≤ 1 ∨ w (t:K c t)⁻¹ ≤ 1 := by
  by_cases h : w (t:K c t) ≤ 1
  · exact Or.inl h
  · right
    have hp : 0<w (t:K c t) := lt_trans zero_lt_one (lt_of_not_ge h)
    rw [map_inv₀,inv_eq_one_div]
    exact (div_le_iff₀ hp).mpr (by simpa only [one_mul] using (le_of_lt (lt_of_not_ge h)))

/-- Both actual normal charts recover precisely the same old center.
This is point coverage, not an asserted sheaf transition or Hodge gluing. -/
theorem center_covered :
    (∃ h : w (t:K c t) ≤ 1,
      Spec.map (CommRingCat.ofHom (OriginalNormalOrderIntegralPoint318.evaluation c t w D M h)) ≫
        OriginalNormalOrderChart318.chart c t w D M=M.center) ∨
    (∃ h : w (t:K c t)⁻¹ ≤ 1,
      Spec.map (CommRingCat.ofHom (evaluation c t w D M h)) ≫
        OriginalNormalInfinityChart318.chart c t w D M=M.center) := by
  rcases coordinate_dichotomy c t w with h|h
  · exact Or.inl ⟨h,OriginalNormalOrderSameCenter318.same_center c t w D M h⟩
  · exact Or.inr ⟨h,same_center c t w D M h⟩
end OriginalNormalInfinitySameCenter318
