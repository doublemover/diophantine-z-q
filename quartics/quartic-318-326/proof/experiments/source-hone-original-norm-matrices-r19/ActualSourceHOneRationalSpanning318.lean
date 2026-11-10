module
public import ActualSourceHOneFiveSpanning318
public import ActualHOneRationalStructures318
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms

public section
noncomputable section
namespace ActualSourceHOneRationalSpanning318
open ActualSourceHOnePrincipalRepresentatives318 ActualSourceHOneSmallPoles318
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The structural sheaf-scalar action on the unchanged actual source H1.
This is not a rational structure inferred from the additive five-slot surjection. -/
instance sourceRationalModule : Module ℚ HOne := ActualHOneRational318.sourceModule

/-- The actual boundary is rational-linear because additive maps between
rational modules preserve their unique rational scalar action. -/
@[expose] def boundaryLinear : ActualSourceHOneCoordinates318.OverlapRing →ₗ[ℚ] HOne :=
  boundary.toRatLinearMap

@[expose] def differenceLinear :
    (ActualSourceHOneCoordinates318.FiniteRing × ActualSourceHOneCoordinates318.InfinityRing) →ₗ[ℚ]
      ActualSourceHOneCoordinates318.OverlapRing :=
  ActualSourceHOneCoordinates318.difference.toRatLinearMap

/-- The original chart-image kernel is a genuine rational subspace. -/
theorem kernel_eq_range : boundaryLinear.ker = differenceLinear.range := by
  ext x
  change x ∈ ActualSourceHOneCoordinates318.boundary.ker ↔
    x ∈ ActualSourceHOneCoordinates318.difference.range
  rw [ActualSourceHOneCoordinates318.kernel_eq_range]

/-- A rational quotient presentation of the same H1, with the kernel identified
above as precisely the original two chart images. -/
@[expose] def kernelQuotientEquivalence :
    (ActualSourceHOneCoordinates318.OverlapRing ⧸ boundaryLinear.ker) ≃ₗ[ℚ] HOne :=
  boundaryLinear.quotKerEquivOfSurjective ActualSourceHOneCoordinates318.boundary_surjective

theorem kernelQuotientEquivalence_mk (x : ActualSourceHOneCoordinates318.OverlapRing) :
    kernelQuotientEquivalence (Submodule.Quotient.mk x) = boundary x :=
  rfl

/-- The exact previously constructed five coefficient maps, now rational-linear. -/
@[expose] def fiveLinear : (SmallIndex → ℚ) →ₗ[ℚ] HOne :=
  ActualSourceHOneFiveSpanning318.fiveCoefficients.toRatLinearMap

theorem fiveLinear_apply (q : SmallIndex → ℚ) :
    fiveLinear q = ActualSourceHOneFiveSpanning318.fiveCoefficients q := rfl

theorem fiveLinear_surjective : Function.Surjective fiveLinear :=
  ActualSourceHOneFiveSpanning318.fiveCoefficients_surjective

instance sourceFiniteDimensional : FiniteDimensional ℚ HOne :=
  FiniteDimensional.of_surjective fiveLinear fiveLinear_surjective

/-- Genuine rational dimension bound for the original whole-source H1. -/
theorem source_finrank_le_five : Module.finrank ℚ HOne ≤ 5 := by
  have h := LinearMap.finrank_le_finrank_of_surjective fiveLinear_surjective
  simpa only [Module.finrank_pi,smallIndex_card] using h

end ActualSourceHOneRationalSpanning318
