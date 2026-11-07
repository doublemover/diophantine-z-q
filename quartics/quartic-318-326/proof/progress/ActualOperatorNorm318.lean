module
public import TangentMetric318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LocalFrameEmbedding318 FrameTransition318
open TangentCoordinates318 ActualQuadraticForm318 TangentMetric318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace ActualOperatorNorm318
set_option maxHeartbeats 0
variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out

theorem descended_norm_formula (b:Base (image N)) (q:fibers N b) :
    PeterssonQuotient318.norm (image N) q.val=
      ‖chosenLinearEquiv N b q‖*(2*(chosenLift N b).im)^2 := by
  let c:=chosenLift N b
  let hc:=chosenLift_mem N hN.out b
  have he:frameMap N hN.out c (⟨b,hc⟩,chosenLinearEquiv N b q)=q.val := by
    rw [←frame_symm_val]
    exact congrArg Subtype.val ((chosenFrame N hN.out b).symm_apply_apply q)
  rw [←he,frameMap_norm,PeterssonTransition318.uniformizing_norm,chosen_sheet_lift]

private theorem scale_cancel (a b c s:ℝ) (hs:s≠0) :
    a*b*c=(a*s^2)*(b/s)*(c/s) := by field_simp

/-- Exact norm evaluation on genuine tangent vectors. The normalization is
that dual to the source cotangent basis of length 2 Imτ. -/
theorem evaluation_norm (b:Base (image N)) (q:fibers N b) (u v:TangentSpace 𝓘(ℂ) b) :
    ‖quadraticEquiv N b q u v‖=
      PeterssonQuotient318.norm (image N) q.val*tangentSeminorm N b u*tangentSeminorm N b v := by
  rw [quadraticEquiv_apply,norm_mul,norm_mul,descended_norm_formula,
    tangentSeminorm_apply,tangentSeminorm_apply]
  exact scale_cancel _ _ _ _ (by positivity)

/-- An actual tangent vector attaining unit length in the specified metric. -/
@[expose] def unitVector (b:Base (image N)) : TangentSpace 𝓘(ℂ) b :=
  ((2*(chosenLift N b).im:ℝ):ℂ)

theorem unitVector_length (b:Base (image N)) : tangentSeminorm N b (unitVector N b)=1 := by
  rw [tangentSeminorm_apply]
  change ‖((2*(chosenLift N b).im:ℝ):ℂ)‖/(2*(chosenLift N b).im)=1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity),div_self (by positivity)]

/-- The actual bilinear norm bound is attained by two actual unit vectors. -/
theorem norm_attained (b:Base (image N)) (q:fibers N b) :
    ‖quadraticEquiv N b q (unitVector N b) (unitVector N b)‖=
      PeterssonQuotient318.norm (image N) q.val := by
  rw [evaluation_norm,unitVector_length,mul_one,mul_one]

/-- The descended Petersson norm is exactly the optimal bilinear operator
bound, not only an upper estimate or an assumed geometric norm identity. -/
theorem operator_bound_iff (b:Base (image N)) (q:fibers N b) (C:ℝ) :
    (∀u v:TangentSpace 𝓘(ℂ) b,‖quadraticEquiv N b q u v‖≤
      C*tangentSeminorm N b u*tangentSeminorm N b v) ↔
    PeterssonQuotient318.norm (image N) q.val≤C := by
  constructor
  · intro h
    have hh:=h (unitVector N b) (unitVector N b)
    rwa [norm_attained,unitVector_length,mul_one,mul_one] at hh
  · intro h u v
    rw [evaluation_norm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (apply_nonneg _ _)) (apply_nonneg _ _)

/-- Equivalent least-upper-bound characterization on the actual metric unit balls. -/
theorem unit_ball_bound_iff (b:Base (image N)) (q:fibers N b) (C:ℝ) :
    (∀u v:TangentSpace 𝓘(ℂ) b,tangentSeminorm N b u≤1→tangentSeminorm N b v≤1→
      ‖quadraticEquiv N b q u v‖≤C) ↔ PeterssonQuotient318.norm (image N) q.val≤C := by
  constructor
  · intro h
    simpa only [norm_attained] using h (unitVector N b) (unitVector N b)
      (le_of_eq (unitVector_length N b)) (le_of_eq (unitVector_length N b))
  · intro h u v hu hv
    rw [evaluation_norm]
    calc
      _≤PeterssonQuotient318.norm (image N) q.val*1*1:=
        mul_le_mul (mul_le_mul_of_nonneg_left hu (norm_nonnegative _ _)) hv
          (apply_nonneg _ _) (by simpa using norm_nonnegative (image N) q.val)
      _≤C:=by simpa using h

end ActualOperatorNorm318
