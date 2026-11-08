module
public import LiteralPlaneJAtlas318
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public section
noncomputable section
open scoped Manifold ContDiff
namespace LiteralPlaneAmbientAnalytic318
open LiteralThreePlanePoints318 LiteralPlaneJAtlas318 LiteralThreePlaneGraph318
set_option maxHeartbeats 400000

/-- The literal inclusion into the original two complex coordinates is
analytic for the target atlas whose inverse germs were independently
identified with the quartic's analytic graph. -/
theorem coordinates_analytic :
    letI := LiteralPlaneJAtlas318.complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ω coordinates := by
  letI := LiteralPlaneJAtlas318.complexChartedSpace
  intro p
  apply contMDiffAt_iff.mpr
  refine ⟨coordinates_continuous.continuousAt, ?_⟩
  change ContDiffWithinAt ℂ ω (fun z => coordinates ((localChart p).symm z)) _
    (localChart p p)
  rw [localChart_apply]
  exact (inverse_coordinates_analytic p).contDiffAt.contDiffWithinAt

/-- The actual derivative of the ambient inverse-chart germ. Its first
coordinate is the identity, not an arbitrary nonzero normalization. -/
@[expose] def graphTangent (p : Plane) : ℂ →L[ℂ] ℂ × ℂ :=
  (ContinuousLinearMap.id ℂ ℂ).prod (fderiv ℂ (graph p) (planeJ p))

theorem inverse_coordinates_hasFDerivAt (p : Plane) :
    HasFDerivAt (fun z : ℂ => coordinates ((localChart p).symm z))
      (graphTangent p) (planeJ p) := by
  have hg := (hasFDerivAt_id (𝕜 := ℂ) (planeJ p)).prodMk
    ((graph_spec p).1.differentiableAt.hasFDerivAt)
  exact hg.congr_of_eventuallyEq (inverse_coordinates_germ p)

theorem graphTangent_fst (p : Plane) (z : ℂ) : (graphTangent p z).1 = z := rfl

/-- Injectivity of the actual local ambient derivative follows from its
proved first-coordinate identity; no generic-point argument is used. -/
theorem graphTangent_injective (p : Plane) : Function.Injective (graphTangent p) := by
  intro z w h
  exact (graphTangent_fst p z).symm.trans
    ((congrArg Prod.fst h).trans (graphTangent_fst p w))

theorem inverse_coordinates_fderiv_injective (p : Plane) :
    Function.Injective
      (fderiv ℂ (fun z : ℂ => coordinates ((localChart p).symm z)) (planeJ p)) := by
  rw [(inverse_coordinates_hasFDerivAt p).fderiv]
  exact graphTangent_injective p

end LiteralPlaneAmbientAnalytic318
