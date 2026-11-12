module
public import IntegralGlobalHeightOne318
public section
noncomputable section
namespace IntegralGlobalLocalCompletion318
open IntegralGlobalHeightOne318 Ring
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] [IsDomain R] [Algebra R ℚ]
  [IsIntegrallyClosed R] [IsNoetherianRing R] (c : Fin 4 → Rˣ)
  (hR : Function.Injective (algebraMap R ℚ)) (h2 : IsUnit (2 : R))
  (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R))
  (x : IntegralGluedModel318.scheme R c) (hx : ringKrullDim (Stalk R c x)=1)
local instance actualStalkDomain : IsDomain (Stalk R c x) := stalk_domain R c hR x
local instance actualStalkDVR : IsDiscreteValuationRing (Stalk R c x) := stalk_dvr R c hR h2 hN x hx

/-- Actual completion of the actual original model stalk, not a chosen
complete DVR receiving only its generic field. -/
abbrev Completion := ActualDVRCompletion318.Completion (Stalk R c x)

theorem completion_dvr : IsDiscreteValuationRing (Completion R c hR h2 hN x hx) :=
  inferInstance

theorem completion_injective : Function.Injective
    (algebraMap (Stalk R c x) (Completion R c hR h2 hN x hx)) :=
  ActualDVRCompletion318.completion_injective (Stalk R c x)

theorem completion_faithfullyFlat :
    Module.FaithfullyFlat (Stalk R c x) (Completion R c hR h2 hN x hx) :=
  CompletionDescent318.completion_faithfullyFlat (Stalk R c x)

/-- The normalization of every original local valuation is unchanged by
actual completion; no ramification factor is suppressed. -/
theorem completion_value (a : Stalk R c x) :
    IsDiscreteValuationRing.addVal (Completion R c hR h2 hN x hx)
      (algebraMap (Stalk R c x) (Completion R c hR h2 hN x hx) a) =
        IsDiscreteValuationRing.addVal (Stalk R c x) a :=
  ActualDVRCompletion318.completion_value (Stalk R c x) a
end IntegralGlobalLocalCompletion318
