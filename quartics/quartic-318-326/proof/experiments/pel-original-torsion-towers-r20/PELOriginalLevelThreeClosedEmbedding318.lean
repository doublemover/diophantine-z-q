module
public import PELOriginalLevelThreePointSeparation318
public import PELOriginalAllLevelHolomorphicMap318
public import ComplexProjectiveCompactTarget318
public import Mathlib.Topology.Maps.Proper.Basic
public section
noncomputable section
namespace PELOriginalLevelThreeClosedEmbedding318
open Set Topology QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open PELOriginalLevelTheta318 ComplexProjectiveQuotientTopology318
variable (τ:ℂ)(hτ:0<τ.im)
abbrev Target:=PELOriginalAllLevelHolomorphicMap318.Target 1
local instance targetTopology:TopologicalSpace Target:=topology (Label 3)
local instance targetHausdorff:T2Space Target:=
  ComplexProjectiveHermitianProjector318.hausdorff (Label 3)
local instance targetCompact:CompactSpace Target:=
  ComplexProjectiveCompactTarget318.compact (Label 3)
local instance sourceCompact:CompactSpace (Base τ):=
  PELComplexPeriodSurface318.surface_compact τ hτ

/-- The nine SAME actual original sections give a genuine CLOSED
TOPOLOGICAL embedding into the independently constructed projective target.
The original source topology is not pulled back from this map. -/
theorem closed_embedding:IsClosedEmbedding (projectiveMap τ hτ 1):=
  (PELOriginalAllLevelHolomorphicMap318.original_continuous τ hτ 1).isClosedEmbedding
    (PELOriginalLevelThreePointSeparation318.injective τ hτ)
theorem proper:IsProperMap (projectiveMap τ hτ 1):=
  (PELOriginalAllLevelHolomorphicMap318.original_continuous τ hτ 1).isProperMap
@[expose] def image:Set Target:=Set.range (projectiveMap τ hτ 1)
theorem image_compact:IsCompact (image τ hτ):=
  isCompact_range (PELOriginalAllLevelHolomorphicMap318.original_continuous τ hτ 1)
theorem image_closed:IsClosed (image τ hτ):=(image_compact τ hτ).isClosed

/-- Exact homeomorphism onto the actual compact closed image, not an
abstract replacement of the original torus or its projective image. -/
@[expose] def imageHomeomorph:Base τ≃ₜimage τ hτ:=
  (closed_embedding τ hτ).isEmbedding.toHomeomorph
@[simp] lemma imageHomeomorph_value(q:Base τ):
    (imageHomeomorph τ hτ q).val=projectiveMap τ hτ 1 q:=rfl
lemma original_covering_image(z:ComplexVectors):
    (imageHomeomorph τ hτ (projection (P τ) z)).val=coveringMap τ hτ 1 z:=
  original_covering_square τ hτ 1 z

/-- The distinction is intentional: properness and closed topological
embedding are now proved, while tangent injectivity, complex-submanifold
structure of the image and algebraization remain subsequent obligations. -/
theorem actual_original_topological_model:
    IsProperMap (projectiveMap τ hτ 1)∧IsClosedEmbedding (projectiveMap τ hτ 1)∧
      IsCompact (image τ hτ):=
  ⟨proper τ hτ,closed_embedding τ hτ,image_compact τ hτ⟩
end PELOriginalLevelThreeClosedEmbedding318
