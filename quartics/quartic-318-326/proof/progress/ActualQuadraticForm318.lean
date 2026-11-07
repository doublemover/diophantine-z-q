module
public import ComplexQuadraticForms318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LinearCocycleBinding318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 CotangentTransition318
open TangentCoordinates318 ComplexQuadraticForms318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace ActualQuadraticForm318
set_option maxHeartbeats 0
variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out

/-- Genuine continuous bilinear forms on the actual Mathlib tangent fiber. -/
abbrev Forms (b:Base (image N)) :=
  TangentSpace 𝓘(ℂ) b→L[ℂ]TangentSpace 𝓘(ℂ) b→L[ℂ]ℂ

/-- The actual orbit fiber, with its registered vector-space structure, is
linearly equivalent to all genuine bilinear forms on the tangent line. -/
@[expose] def quadraticEquiv (b:Base (image N)) : fibers N b ≃ₗ[ℂ] Forms N b :=
  (chosenLinearEquiv N b).trans coefficientEquiv

theorem quadraticEquiv_apply (b:Base (image N)) (q:fibers N b)
    (u v:TangentSpace 𝓘(ℂ) b) :
    quadraticEquiv N b q u v=chosenLinearEquiv N b q*(show ℂ from u)*(show ℂ from v) :=
  coefficientEquiv_apply _ _ _

theorem coefficient_in_chart (a:UpperHalfPlane) (b:Base (image N))
    (hb:b∈sheet N hN.out a) (q:fibers N b) :
    (dependentTrivialization N hN.out a ⟨b,q⟩).2=
      chosenLinearEquiv N b q /
        (deriv ((localChart N hN.out (chosenLift N b)).symm.trans (localChart N hN.out a))
          (localChart N hN.out (chosenLift N b) b))^2 := by
  let c:=chosenLift N b
  let hc:=chosenLift_mem N hN.out b
  have he:frameMap N hN.out c (⟨b,hc⟩,chosenLinearEquiv N b q)=q.val := by
    rw [←frame_symm_val]
    exact congrArg Subtype.val ((chosenFrame N hN.out b).symm_apply_apply q)
  change (trivialization N hN.out a q.val).2=_
  rw [←he,cotangent_square_transition N hN.out c a b hc hb]
  rfl

private theorem cancel_square (q d u v:ℂ) (hd:d≠0) :
    q*u*v=(q/d^2)*(d*u)*(d*v) := by
  field_simp

/-- Evaluation is independent of the chosen chart: the actual orbit
coefficient paired with two actual tangent coordinates gives the same form. -/
theorem chart_evaluation (a:UpperHalfPlane) (b:Base (image N))
    (hb:b∈sheet N hN.out a) (q:fibers N b) (u v:TangentSpace 𝓘(ℂ) b) :
    quadraticEquiv N b q u v=
      (dependentTrivialization N hN.out a ⟨b,q⟩).2*
      (tangentFrame N a ⟨b,u⟩).2*(tangentFrame N a ⟨b,v⟩).2 := by
  rw [quadraticEquiv_apply,coefficient_in_chart N a b hb,tangent_frame_apply,tangent_frame_apply]
  have hd:=transition_derivative_ne_zero N hN.out (chosenLift N b) a _
    (chart_transition_mem N hN.out (chosenLift N b) a b ⟨chosenLift_mem N hN.out b,hb⟩)
  dsimp only
  exact cancel_square _ _ (show ℂ from u) (show ℂ from v) hd

/-- In complex dimension one every continuous bilinear form is symmetric. -/
theorem quadratic_symmetric (b:Base (image N)) (q:fibers N b)
    (u v:TangentSpace 𝓘(ℂ) b) : quadraticEquiv N b q u v=quadraticEquiv N b q v u :=
  ComplexQuadraticForms318.symmetric _ _ _

/-- The identification also respects the actual fiber topology. -/
@[expose] def quadraticHomeomorph (b:Base (image N)) : fibers N b ≃L[ℂ] Forms N b where
  __:=quadraticEquiv N b
  continuous_toFun:=by
    change Continuous (fun q:fibers N b=>chosenFrame N hN.out b q • ContinuousLinearMap.mul ℂ ℂ)
    exact (chosenFrame N hN.out b).continuous.smul continuous_const
  continuous_invFun:=by
    change Continuous (fun B:ℂ→L[ℂ]ℂ→L[ℂ]ℂ=>(chosenFrame N hN.out b).symm (B 1 1))
    apply (chosenFrame N hN.out b).symm.continuous.comp
    fun_prop

end ActualQuadraticForm318
