module
public import ActualSourceHOneCoordinates318
public import ContactGlobalSigns318
public import StableCoverBoundary318

public section
noncomputable section
namespace OriginalSignChartPreservation318
open AlgebraicGeometry CategoryTheory
open ActualSourceHOnePresentation318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev units := SourceTwistArithmetic318.units
abbrev signMap (b : Fin 4 → Bool) := ContactGlobalSigns318.map units b

/-- The entire finite chart is invariant because the original sign extension lies over the original line. -/
theorem finite_preimage (b : Fin 4 → Bool) : signMap b ⁻¹ᵁ finiteOpen = finiteOpen := by
  rw [show finiteOpen = (SourceGlobalAffine318.actualOpen units).1 from
    SourceGlobalAffine318.chartEmbedding_range units]
  change signMap b ⁻¹ᵁ ((ContactProjectiveModel318.modelMap units) ⁻¹ᵁ
    (JLineAtlas318.chart ℚ 1 ''ᵁ ⊤)) = _
  rw [← Scheme.Hom.comp_preimage,ContactGlobalSigns318.over_line]

/-- The whole infinity neighborhood, not just its generic point, is invariant as well. -/
theorem infinity_preimage (b : Fin 4 → Bool) : signMap b ⁻¹ᵁ infinityOpen = infinityOpen := by
  rw [show infinityOpen = (InfinityGlobalScheme318.actualOpen units).1 from
    InfinityGlobalScheme318.chartEmbedding_range units]
  change signMap b ⁻¹ᵁ ((ContactProjectiveModel318.modelMap units) ⁻¹ᵁ
    (InfinityGlobalBase318.baseOpen units ''ᵁ ⊤)) = _
  rw [← Scheme.Hom.comp_preimage,ContactGlobalSigns318.over_line]

theorem overlap_preimage (b : Fin 4 → Bool) :
    signMap b ⁻¹ᵁ (finiteOpen ⊓ infinityOpen) = finiteOpen ⊓ infinityOpen := by
  rw [Scheme.Hom.preimage_inf,finite_preimage,infinity_preimage]

local instance originalOpen : IsOpenImmersion (ContactProjectiveModel318.sourceOpen units) :=
  ContactProjectiveModel318.sourceOpen_open units

/-- The original global sign's actual overlap section pullback is the original root-sign algebra map. -/
theorem overlap_sections (b : Fin 4 → Bool) (x : ActualSourceHOneCoordinates318.OverlapRing) :
    (signMap b).appLE (finiteOpen ⊓ infinityOpen) (finiteOpen ⊓ infinityOpen)
      (le_of_eq (overlap_preimage b).symm)
      (ActualSourceHOneCoordinates318.overlapSections x) =
    ActualSourceHOneCoordinates318.overlapSections (ContactGlobalSigns318.openEquiv units b x) := by
  exact StableCoverBoundary318.affine_coordinates
    (ContactProjectiveModel318.sourceOpen units) (signMap b)
    (ContactGlobalSigns318.openEquiv units b).toRingHom (ContactGlobalSigns318.on_open units b)
    (finiteOpen ⊓ infinityOpen) (ContactFullOverlap318.actual_full_intersection units).symm
    (overlap_preimage b) x

end OriginalSignChartPreservation318
