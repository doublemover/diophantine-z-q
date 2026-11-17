module
public import PELOriginalLevelThreeLocalImage318
public import SplitHolomorphicAmbientChart318
public section
noncomputable section
namespace PELOriginalLevelThreeAmbientImage318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLevelThetaStrictDerivative318
open PELOriginalLevelThreeLocalImage318 SplitHolomorphicImage318
open SplitHolomorphicGraphCoordinates318 SplitHolomorphicAmbientChart318 Set
variable (τ:ℂ) (hτ:0<τ.im) (x:ComplexVectors) (j:Label 3)
  (hj:value τ hτ 3 j x≠0)
local notation "f" => ratioVector τ hτ 1 j
local notation "A" => fderiv ℂ f x
local notation "K" => Normal A
local notation "hf" => ratio_contDiffAt τ hτ 1 j x hj
local notation "hi" => PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ x j hj

/-- The actual local image is a complex surface in an independently
constructed ambient chart: it is exactly the zero normal-coordinate
slice. Both ambient coordinate maps are genuinely holomorphic. -/
theorem actual_ambient_chart:
    ∃W:Set ComplexVectors,IsOpen W ∧ projection A (f x)∈W ∧
    ∃e:OpenPartialHomeomorph (TargetModel 1) (ComplexVectors×K),
      e.source=projection A ⁻¹' W ∧ e.target=Prod.fst ⁻¹' W ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (∀w∈W,(parameterChart τ hτ x j hj).symm w∈originalChartDomain τ hτ x j) ∧
      e '' (f '' ((parameterChart τ hτ x j hj).source ∩
        (fun z=>projection A (f z)) ⁻¹' W))=
        {q:ComplexVectors×K|q.1∈W ∧ q.2=0}:=by
  obtain ⟨W,hW,hWx,ht,hg,hU,hp,himage⟩:=local_holomorphic_image τ hτ x j hj
  have hv:DifferentiableOn ℂ (vertical f x hf hi) W:=
    vertical_holomorphicOn f x hf hi W hg
  let e:=ambientChart f x hf hi W hW hv.continuousOn
  refine ⟨W,hW,hWx,e,rfl,rfl,
    ambient_holomorphic f x hf hi W hW hv,
    ambient_inverse_holomorphic f x hf hi W hW hv,hU,?_⟩
  rw [himage]
  exact flattened_image f x hf hi W hW hv.continuousOn ht
end PELOriginalLevelThreeAmbientImage318
