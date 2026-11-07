module
public import PeterssonQuotient318
public import Mathlib.Topology.Constructions
public section
noncomputable section
open DerivativeCocycle318 QuadraticFiber318 PeterssonQuotient318
namespace ContinuousDescent318
set_option maxHeartbeats 0

@[expose] def coordinates (v:Fiber) : Prod UpperHalfPlane ℂ := (v.point,v.value)
instance : TopologicalSpace Fiber := TopologicalSpace.induced coordinates inferInstance

@[fun_prop] theorem continuous_point : Continuous Fiber.point :=
  continuous_fst.comp (continuous_induced_dom (f:=coordinates))
@[fun_prop] theorem continuous_value : Continuous Fiber.value :=
  continuous_snd.comp (continuous_induced_dom (f:=coordinates))

theorem fiberNorm_formula (v:Fiber) : fiberNorm v=‖v.value‖*(2*v.point.im)^2 :=
  PeterssonTransition318.uniformizing_norm _ _

theorem continuous_fiberNorm : Continuous fiberNorm := by
  change Continuous (fun v:Fiber=>fiberNorm v)
  simp_rw [fiberNorm_formula]
  fun_prop

/-- Actual quotient topology and an actual continuous descended norm. -/
theorem continuous_norm (H:Subgroup G) : Continuous (PeterssonQuotient318.norm H) := by
  apply Continuous.quotient_lift
  exact continuous_fiberNorm

end ContinuousDescent318
#print axioms ContinuousDescent318.continuous_norm
