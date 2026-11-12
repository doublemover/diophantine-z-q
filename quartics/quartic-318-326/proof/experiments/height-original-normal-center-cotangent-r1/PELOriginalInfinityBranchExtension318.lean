module
public import PELOriginalInfinityBranchSource318
public import PELOriginalGluedCoordinatesHolomorphy318
public import LegendrePuncturedInfinityExtension318
public section
noncomputable section
namespace PELOriginalInfinityBranchExtension318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRegularCoverPatches318
open PELOriginalGluedLegendreMap318 PELOriginalCompletedLegendreBijection318
open PELOriginalInfinityBranchSource318
open NormalizedLegendreProjectiveModel318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

/-- For the FIXED original completed comparison, all punctured infinity
inputs are produced from actual original source holomorphy and equation.
Its native target U,V coordinates extend analytically through (0,0), with
U a genuine invertible local coordinate. No prior target chart-membership
or continuity at infinity is required. -/
theorem infinity_branch (p:CharacterBase i) (hp:normalizedMap i p=∞) :
    ∃U V k:ℂ→ℂ,AnalyticAt ℂ U 0 ∧ AnalyticAt ℂ V 0 ∧ U 0=0 ∧ V 0=0 ∧
      deriv U 0≠0 ∧ AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun w=>k (U w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>U (k w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ w in 𝓝 (0:ℂ),LegendreInfinityBranchGerm318.equation (branchParameter i) (U w) (V w)=0) ∧
      (∀ᶠ w in 𝓝[≠] (0:ℂ),
        U w=((coordinates i (source i p hp w)).1-shift (branchParameter i))/
          (coordinates i (source i p hp w)).2 ∧
        V w=((coordinates i (source i p hp w)).2)⁻¹) ∧
      completedMap i (source i p hp 0)=none := by
  let l:=branchParameter i
  let g:=source i p hp
  let y:ℂ→ℂ:=fun w=>(coordinates i (g w)).2
  have hreg:∀ᶠ w in 𝓝[≠] (0:ℂ),g w∈Regular i:=source_regular i p hp
  have hy:∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ y w:=by
    filter_upwards [hreg,(source_holomorphic i p hp).filter_mono nhdsWithin_le_nhds] with w hr hg
    exact (PELOriginalGluedCoordinatesHolomorphy318.along_holomorphic_curve i g w hg hr).2.differentiableAt
  have hcoord:∀ᶠ w in 𝓝[≠] (0:ℂ),(coordinates i (g w)).1=(w^2)⁻¹:=by
    filter_upwards [hreg,source_punctured_projection i p hp] with w hr hproj
    exact OnePoint.coe_injective ((coordinates_projection i (g w) hr).trans hproj)
  have he:∀ᶠ w in 𝓝[≠] (0:ℂ),y w^2=LegendreHalfPlaneAnalyticSheets318.polynomial l ((w^2)⁻¹):=by
    filter_upwards [hreg,hcoord] with w hr hc
    have hh:=coordinates_equation i (g w) hr
    rw [hc] at hh
    exact hh
  obtain ⟨Y,hY,hY0,hYf,hunit,hU,hV,hU0,hV0,hUd,heq,hformula⟩:=
    LegendrePuncturedInfinityExtension318.extend l y hy he
  let U:=LegendrePuncturedInfinityExtension318.nativeU l Y
  let V:=LegendrePuncturedInfinityExtension318.nativeV Y
  obtain ⟨k,hk,hk0,hleft,hright⟩:=FiniteAnalyticCharts318.analytic_inverse hU hUd
  rw [hU0] at hk hk0 hright
  refine ⟨U,V,k,hU,hV,hU0,hV0,hUd,hk,hk0,hleft,hright,heq,?_,?_⟩
  · filter_upwards [hformula,hcoord] with w hw hc
    rw [hc]
    exact hw
  · rw [source_zero i p hp]
    apply completedMap_branch i p (Or.inl hp)
    exact hp.symm
end PELOriginalInfinityBranchExtension318
