module
public import LiteralPlaneJAtlas318
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph
public section
noncomputable section
open scoped Manifold ContDiff
namespace LiteralPlaneBiholomorph318
open ThreeArithmeticQuotient318 LiteralThreePlanePoints318 LiteralPlaneComparison318
set_option maxHeartbeats 400000

/-- The original comparison is analytic in the actual source and target j
charts. Its continuity is that of the original homeomorphism. -/
theorem comparison_analytic (N : ℕ) [NeZero N] :
    letI:=AdmissibleJComplexAtlas318.complexChartedSpace
    letI:=LiteralPlaneJAtlas318.complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (comparison N) := by
  letI:=AdmissibleJComplexAtlas318.complexChartedSpace
  letI:=LiteralPlaneJAtlas318.complexChartedSpace
  intro q
  apply contMDiffAt_iff_target.mpr
  refine ⟨(comparison N).continuous.continuousAt,?_⟩
  have he : (extChartAt 𝓘(ℂ) (comparison N q) ∘ comparison N)=extChartAt 𝓘(ℂ) q := by
    funext p
    change LiteralPlaneJAtlas318.localChart (comparison N q) (comparison N p)=
      AdmissibleJComplexAtlas318.localChart q p
    rw [LiteralPlaneJAtlas318.localChart_apply,
      AdmissibleJComplexAtlas318.localChart_apply,comparison_j]
  rw [he]
  exact contMDiffAt_extChartAt

/-- The actual inverse comparison is analytic, using its proved exact inverse
j identity and the original inverse's continuity. -/
theorem comparison_inverse_analytic (N : ℕ) [NeZero N] :
    letI:=AdmissibleJComplexAtlas318.complexChartedSpace
    letI:=LiteralPlaneJAtlas318.complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (comparison N).symm := by
  letI:=AdmissibleJComplexAtlas318.complexChartedSpace
  letI:=LiteralPlaneJAtlas318.complexChartedSpace
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨(comparison N).symm.continuous.continuousAt,?_⟩
  have he : (extChartAt 𝓘(ℂ) ((comparison N).symm p) ∘ (comparison N).symm)=
      extChartAt 𝓘(ℂ) p := by
    funext q
    change AdmissibleJComplexAtlas318.localChart ((comparison N).symm p)
      ((comparison N).symm q)=LiteralPlaneJAtlas318.localChart p q
    rw [AdmissibleJComplexAtlas318.localChart_apply,
      LiteralPlaneJAtlas318.localChart_apply,comparison_symm_j]
  rw [he]
  exact contMDiffAt_extChartAt

/-- Analytic equivalence with the exact original forward and inverse maps.
The target atlas's independent ambient graph compatibility is supplied by
LiteralPlaneJAtlas318, not inferred from this equivalence. -/
@[expose] def biholomorph (N : ℕ) [NeZero N] :
    letI:=AdmissibleJComplexAtlas318.complexChartedSpace
    letI:=LiteralPlaneJAtlas318.complexChartedSpace
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Source Plane ω := by
  letI:=AdmissibleJComplexAtlas318.complexChartedSpace
  letI:=LiteralPlaneJAtlas318.complexChartedSpace
  exact { toEquiv := (comparison N).toEquiv
          contMDiff_toFun := comparison_analytic N
          contMDiff_invFun := comparison_inverse_analytic N }

lemma biholomorph_apply (N : ℕ) [NeZero N] (q : Source) :
    letI:=AdmissibleJComplexAtlas318.complexChartedSpace
    letI:=LiteralPlaneJAtlas318.complexChartedSpace
    biholomorph N q=comparison N q := rfl

lemma biholomorph_inverse_apply (N : ℕ) [NeZero N] (p : Plane) :
    letI:=AdmissibleJComplexAtlas318.complexChartedSpace
    letI:=LiteralPlaneJAtlas318.complexChartedSpace
    (biholomorph N).symm p=(comparison N).symm p := rfl

end LiteralPlaneBiholomorph318
