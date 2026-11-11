module
public import ProjectiveLineBiholomorph318
public section
noncomputable section
open Function Filter Topology
open scoped Manifold ContDiff
namespace ActualThreeProjectivePoints318
open ProjectiveLineFieldPoints318 ProjectiveLinePointEquiv318
open ProjectiveLineComplexTopology318 ProjectiveLineComplexAtlas318 ProjectiveLineBiholomorph318
open ActualThreeCuspFilling318 ActualThreeFilledParameter318 ActualThreeCuspExhaustion318
open ActualThreeComplexAtlas318 ActualThreeBiholomorph318 ActualThreeExceptionalParameter318
open GammaOneFiber318 PeterssonQuotient318 SphereCharts318

local instance : TopologicalSpace ComplexPoints := complexPointTopology

/-- The original compact modular comparison, with its target now the actual
base-preserving complex-valued points of the original homogeneous Proj over Q. -/
@[expose] def compactPointHomeomorph : Filled ≃ₜ ComplexPoints :=
  compactHomeomorph.trans pointHomeomorph

lemma compactPointHomeomorph_apply (z : Filled) :
    compactPointHomeomorph z = pointHomeomorph (compactHomeomorph z) := rfl

/-- At every original point, including elliptic points, the morphism of schemes
is evaluation at the exact original parameter, not only a matching j value. -/
lemma compactPointHomeomorph_original (b : Base (image 3)) :
    compactPointHomeomorph (original b) = chartPoint (R:=ℚ) 1 (quotientParameter b) := by
  rw [compactPointHomeomorph_apply,compactHomeomorph_original]
  rfl

/-- The original infinite cusp goes to the zero of the original reciprocal
algebraic chart, as an equality of actual scheme-valued points. -/
lemma compactPointHomeomorph_infinity :
    compactPointHomeomorph (cusp infinityEnd) = chartPoint (R:=ℚ) 0 (0:ℂ) := by
  rw [compactPointHomeomorph_apply]
  change pointHomeomorph (compactHomeomorph ActualThreeCuspHausdorff318.infinityCusp)=_
  rw [compactHomeomorph_infinity]
  rfl

/-- The other actual cusp goes to the zero of the original finite algebraic chart. -/
lemma compactPointHomeomorph_zero :
    compactPointHomeomorph (cusp zeroEnd) = chartPoint (R:=ℚ) 1 (0:ℂ) := by
  rw [compactPointHomeomorph_apply]
  change pointHomeomorph (compactHomeomorph ActualThreeCuspHausdorff318.zeroCusp)=_
  rw [compactHomeomorph_zero]
  rfl

/-- Exact analytic comparison with the actual projective scheme's complex
points, using their original polynomial-evaluation chart atlas. The source
atlas retains its separately proved original orbit and cusp-germ meaning. -/
@[expose] def compactPointBiholomorph :
    letI := filledChartedSpace
    letI := pointChartedSpace
    Filled ≃ₘ^ω⟮𝓘(ℂ),𝓘(ℂ)⟯ ComplexPoints := by
  letI := filledChartedSpace
  letI := sphereChartedSpace
  letI := pointChartedSpace
  exact compactBiholomorph.trans pointBiholomorph

lemma compactPointBiholomorph_apply (z : Filled) :
    letI := filledChartedSpace
    letI := pointChartedSpace
    compactPointBiholomorph z = compactPointHomeomorph z := rfl

end ActualThreeProjectivePoints318
