module
public import ActualQuadraticForm318
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LinearCocycleBinding318
open LocalFrameEmbedding318 TangentCoordinates318 ComplexQuadraticForms318 ActualQuadraticForm318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace FormBundleCoordinates318
set_option maxHeartbeats 0
variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out
local instance lineHolomorphic : ContMDiffVectorBundle ω ℂ (fibers N) 𝓘(ℂ) :=
  HolomorphicLineRegistration318.holomorphicVectorBundle N

abbrev FormModel:=ℂ→L[ℂ]ℂ→L[ℂ]ℂ
abbrev FormTotal:=Bundle.TotalSpace FormModel (Forms N)

@[expose] def formMap (p:total N) : FormTotal N := ⟨p.proj,quadraticEquiv N p.proj p.2⟩

@[expose] def formEquiv : total N ≃ FormTotal N where
  toFun:=formMap N
  invFun p:=⟨p.proj,(quadraticEquiv N p.proj).symm p.2⟩
  left_inv p:=by
    rcases p with ⟨b,q⟩
    change (⟨b,(quadraticEquiv N b).symm (quadraticEquiv N b q)⟩:total N)=⟨b,q⟩
    rw [LinearEquiv.symm_apply_apply]
  right_inv p:=by cases p; simp [formMap]

/-- The standard iterated Hom-bundle trivialization of the actual quadratic
forms agrees with the actual orbit coefficient in the same quotient chart. -/
theorem form_coordinates (b₀:Base (image N)) (p:total N)
    (hp:p.proj∈sheet N hN.out (chosenLift N b₀)) :
    trivializationAt FormModel (Forms N) b₀ (formMap N p)=
      (p.proj,coefficientEquiv
        ((dependentTrivialization N hN.out (chosenLift N b₀)) p).2) := by
  have ht:p.proj∈(trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b₀).baseSet := by
    change p.proj∈(localChart N hN.out (chosenLift N b₀)).source
    rw [chart_source]
    exact hp
  have hc:p.proj∈(trivializationAt (ℂ→L[ℂ]ℂ) (fun x=>TangentSpace 𝓘(ℂ) x→L[ℂ]ℂ) b₀).baseSet := by
    exact ⟨ht,Set.mem_univ _⟩
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [hom_trivializationAt_apply,ContinuousLinearMap.inCoordinates,formMap]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R:=ℂ) _ hc]
    simp only [hom_trivializationAt_apply,ContinuousLinearMap.inCoordinates,ContinuousLinearMap.comp_apply]
    have hz:(trivializationAt ℂ (fun _ :Base (image N)=>ℂ) b₀).continuousLinearMapAt ℂ p.proj=
        ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ (Base (image N)) ℂ p.proj
    rw [hz,ContinuousLinearMap.id_apply,coefficientEquiv_apply,
      chart_evaluation N (chosenLift N b₀) p.proj hp]
    have hcoord (w:ℂ) :
        (tangentFrame N (chosenLift N b₀) ⟨p.proj,
          (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b₀).symmL ℂ p.proj w⟩).2=w := by
      change ((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b₀)
        ⟨p.proj,(trivializationAt ℂ (TangentSpace 𝓘(ℂ)) b₀).symmL ℂ p.proj w⟩).2=w
      rw [←Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R:=ℂ) _ ht]
      exact Bundle.Trivialization.continuousLinearMapAt_symmL _ ht w
    rw [hcoord,hcoord]

end FormBundleCoordinates318
