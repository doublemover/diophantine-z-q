module
public import AffineCoverHOnePresentation318
public import ContactGlobalSmooth318
public import ActualSourceHOnePullbacks318
public section
noncomputable section
namespace ActualSourceHOnePresentation318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Source := ContactGlobalSmooth318.Model units
local instance sourceIntegral : IsIntegral Source := ContactProjectiveModel318.model_integral units
abbrev finiteOpen : Source.Opens := (SourceGlobalAffine318.chartEmbedding units).opensRange
abbrev infinityOpen : Source.Opens := (InfinityGlobalScheme318.chartEmbedding units).opensRange

theorem finite_affine : IsAffineOpen finiteOpen := isAffineOpen_opensRange (SourceGlobalAffine318.chartEmbedding units)
theorem infinity_affine : IsAffineOpen infinityOpen := by
  change IsAffineOpen (InfinityGlobalScheme318.chartEmbedding units).opensRange
  rw [InfinityGlobalScheme318.chartEmbedding_range]
  exact (InfinityGlobalScheme318.actualOpen units).2
theorem cover : finiteOpen ⊔ infinityOpen = ⊤ := ContactGlobalSmooth318.actual_charts_cover units

/-- Original functions on the full finite/infinity overlap map to the unchanged common-source H1. -/
@[expose] def boundary : Γ(Source,finiteOpen ⊓ infinityOpen) →+ ActualSourceHOnePullbacks318.SourceHOne :=
  AffineCoverHOnePresentation318.boundary finiteOpen infinityOpen cover

theorem boundary_surjective : Function.Surjective boundary :=
  AffineCoverHOnePresentation318.boundary_surjective finiteOpen infinityOpen finite_affine infinity_affine cover
end ActualSourceHOnePresentation318
