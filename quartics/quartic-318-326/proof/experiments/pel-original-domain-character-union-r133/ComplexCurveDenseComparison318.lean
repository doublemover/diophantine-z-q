module
public import ComplexCurveOpenMapping318
public import DenseTargetOpenComparison318
public section
noncomputable section
namespace ComplexCurveDenseComparison318
open Set
open scoped Manifold ContDiff
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [CompactSpace M]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]

/-- Global comparison of the SAME original compact complex curves.
Holomorphy, a dense open injective interior, and exhaustive regular-target
fibers construct both directions; boundary injectivity is a conclusion. -/
@[expose] def comparison (F : M → N)
    (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (U : Set M) (hU : IsOpen U) (hUd : Dense U) (hinj : InjOn F U)
    (V : Set N) (hVd : Dense V) (hcover : V⊆range F) (hpre : F ⁻¹' V⊆U) : M ≃ₜ N :=
  DenseTargetOpenComparison318.homeomorph F hF.continuous
    (ComplexCurveOpenMapping318.isOpenMap F hF U hU hUd hinj) V hVd hcover
    (DenseTargetOpenComparison318.fibers_of_interior F U V hinj hpre)

/-- Actual forward and inverse holomorphy in the original maximal
atlases, not a complex structure transported along a topological sphere. -/
theorem comparison_biholomorphic (F : M → N)
    (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (U : Set M) (hU : IsOpen U) (hUd : Dense U) (hinj : InjOn F U)
    (V : Set N) (hVd : Dense V) (hcover : V⊆range F) (hpre : F ⁻¹' V⊆U) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison F hF U hU hUd hinj V hVd hcover hpre) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison F hF U hU hUd hinj V hVd hcover hpre).symm := by
  have hh : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison F hF U hU hUd hinj V hVd hcover hpre) := hF
  exact ⟨hh,ComplexCurveHomeomorphInverse318.inverse _ hh⟩
end ComplexCurveDenseComparison318
