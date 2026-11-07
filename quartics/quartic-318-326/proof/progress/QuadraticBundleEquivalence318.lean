module
public import FormBundleCoordinates318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LinearCocycleBinding318
open LocalFrameEmbedding318 TangentCoordinates318 ComplexQuadraticForms318 ActualQuadraticForm318
open FormBundleCoordinates318 Filter Topology Bundle
open scoped Manifold ContDiff
namespace QuadraticBundleEquivalence318
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false

@[expose] def coefficientContinuousEquiv : ℂ ≃L[ℂ] FormModel where
  __:=ComplexQuadraticForms318.coefficientEquiv
  continuous_toFun:=by
    change Continuous (fun q:ℂ=>q • ContinuousLinearMap.mul ℂ ℂ)
    exact (continuous_id:Continuous (fun q:ℂ=>q)).smul continuous_const
  continuous_invFun:=by change Continuous (fun B:FormModel=>B 1 1);fun_prop

variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out
local instance lineHolomorphic : ContMDiffVectorBundle ω ℂ (fibers N) 𝓘(ℂ) :=
  HolomorphicLineRegistration318.holomorphicVectorBundle N

/-- The genuine total-space map to the standard iterated Hom bundle is
holomorphic, rather than merely a family of fiberwise identifications. -/
theorem formMap_holomorphic :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ,FormModel)) ω (formMap N) := by
  intro p₀
  have hi:ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω
      (fun p:total N=>p) p₀:=contMDiffAt_id
  obtain ⟨hb,hq⟩:=contMDiffAt_totalSpace.mp hi
  apply contMDiffAt_totalSpace.mpr
  refine ⟨hb,?_⟩
  have hc:=(ContinuousLinearMap.contMDiff (𝕜:=ℂ) (E:=ℂ) (F:=FormModel) coefficientContinuousEquiv.toContinuousLinearMap).contMDiffAt.comp p₀ hq
  apply hc.congr_of_eventuallyEq
  have hn:∀ᶠp:total N in 𝓝 p₀,p.proj∈sheet N hN.out (chosenLift N p₀.proj) := by
    exact (FiberBundle.continuous_proj ℂ (fibers N)).continuousAt.eventually
      (((quotient_localHomeomorph N hN.out).localInverseAt (chosenLift N p₀.proj)).open_source.mem_nhds
        (chosenLift_mem N hN.out p₀.proj))
  filter_upwards [hn] with p hp
  exact congrArg Prod.snd (form_coordinates N p₀.proj p hp)

/-- Exact inverse coordinate formula in the genuine iterated Hom bundle. -/
theorem inverse_coordinates (b₀:Base (image N)) (p:FormTotal N)
    (hp:p.proj∈sheet N hN.out (chosenLift N b₀)) :
    (dependentTrivialization N hN.out (chosenLift N b₀)) ((formEquiv N).symm p)=
      (p.proj,ComplexQuadraticForms318.coefficientEquiv.symm (trivializationAt FormModel (Forms N) b₀ p).2) := by
  have hh:=form_coordinates N b₀ ((formEquiv N).symm p) hp
  have he:formMap N ((formEquiv N).symm p)=p:=(formEquiv N).apply_symm_apply p
  rw [he] at hh
  apply Prod.ext
  · exact (dependentTrivialization N hN.out (chosenLift N b₀)).proj_toFun _
      ((dependentTrivialization N hN.out (chosenLift N b₀)).mem_source.mpr hp)
  · apply ComplexQuadraticForms318.coefficientEquiv.injective
    rw [ComplexQuadraticForms318.coefficientEquiv.apply_symm_apply]
    exact (congrArg Prod.snd hh).symm

/-- The inverse map is also genuinely holomorphic. -/
theorem inverse_holomorphic :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ,FormModel)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (formEquiv N).symm := by
  intro p₀
  have hi:ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ,FormModel)) (𝓘(ℂ).prod 𝓘(ℂ,FormModel)) ω
      (fun p:FormTotal N=>p) p₀:=contMDiffAt_id
  obtain ⟨hb,hq⟩:=contMDiffAt_totalSpace.mp hi
  apply contMDiffAt_totalSpace.mpr
  refine ⟨hb,?_⟩
  have hc:=(ContinuousLinearMap.contMDiff (𝕜:=ℂ) (E:=FormModel) (F:=ℂ) coefficientContinuousEquiv.symm.toContinuousLinearMap).contMDiffAt.comp p₀ hq
  apply hc.congr_of_eventuallyEq
  have hn:∀ᶠp:FormTotal N in 𝓝 p₀,p.proj∈sheet N hN.out (chosenLift N p₀.proj) := by
    exact (FiberBundle.continuous_proj FormModel (Forms N)).continuousAt.eventually
      (((quotient_localHomeomorph N hN.out).localInverseAt (chosenLift N p₀.proj)).open_source.mem_nhds
        (chosenLift_mem N hN.out p₀.proj))
  filter_upwards [hn] with p hp
  exact congrArg Prod.snd (inverse_coordinates N p₀.proj p hp)

/-- A genuine global homeomorphism with both directions holomorphic. -/
@[expose] def formHomeomorph : total N ≃ₜ FormTotal N where
  __:=formEquiv N
  continuous_toFun:=(formMap_holomorphic N).continuous
  continuous_invFun:=(inverse_holomorphic N).continuous

/-- The global equivalence preserves the actual base point. -/
theorem formHomeomorph_projection (p:total N) : (formHomeomorph N p).proj=p.proj := rfl

/-- Fiberwise addition is preserved by the genuine global bundle equivalence. -/
theorem formHomeomorph_add (b:Base (image N)) (q r:fibers N b) :
    formHomeomorph N ⟨b,q+r⟩=⟨b,quadraticEquiv N b q+quadraticEquiv N b r⟩ := by
  change (⟨b,quadraticEquiv N b (q+r)⟩:FormTotal N)=_
  rw [map_add]

/-- Fiberwise complex scalar multiplication is preserved. -/
theorem formHomeomorph_smul (b:Base (image N)) (c:ℂ) (q:fibers N b) :
    formHomeomorph N ⟨b,c • q⟩=⟨b,c • quadraticEquiv N b q⟩ := by
  change (⟨b,quadraticEquiv N b (c • q)⟩:FormTotal N)=_
  rw [map_smul]

end QuadraticBundleEquivalence318
