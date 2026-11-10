module
public import PELOriginalFiniteBranchSource318
public import LegendrePuncturedFiniteExtension318
public import PELOriginalGluedCoordinatesHolomorphy318
public import PELOriginalCompletedLegendreBijection318
public section
noncomputable section
namespace PELOriginalFiniteBranchExtension318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRegularCoverPatches318
open PELOriginalGluedLegendreMap318 PELOriginalCompletedLegendreBijection318
open LegendreSimpleBranchCharts318 LegendreHalfPlaneAnalyticSheets318
open PELOriginalFiniteBranchSource318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

/-- The FIXED completed map, not a newly selected local cover, is analytic
and locally invertible across EACH original finite branch. Both source and
target use their independently constructed literal square parameters.
Every punctured holomorphy, equation, and central value is derived here. -/
theorem finite_branch (j:Fin 3) (p:CharacterBase i)
    (hp:normalizedMap i p=(branch (branchParameter i) j:OnePoint ℂ)) :
    ∃q k:ℂ→ℂ,AnalyticAt ℂ q 0 ∧ q 0=0 ∧ deriv q 0^2=1 ∧
      AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun w=>k (q w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>q (k w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ w in 𝓝 (0:ℂ),q w^2=w^2) ∧
      AnalyticAt ℂ (fun w=>(LegendreLiteralFiniteBranch318.point (branchParameter i)
        (branchParameter_nonexceptional i).1 (branchParameter_nonexceptional i).2 j (q w)).val) 0 ∧
      (∀ᶠ w in 𝓝 (0:ℂ),completedMap i (source i j p hp w)=
        some (LegendreLiteralFiniteBranch318.point (branchParameter i)
          (branchParameter_nonexceptional i).1 (branchParameter_nonexceptional i).2 j (q w))) := by
  let l:=branchParameter i
  let h0:= (branchParameter_nonexceptional i).1
  let h1:= (branchParameter_nonexceptional i).2
  let a:=branch l j
  let g:=source i j p hp
  let y:ℂ→ℂ:=fun w=>(coordinates i (g w)).2
  have hreg:∀ᶠ w in 𝓝[≠] (0:ℂ),g w∈Regular i:=source_regular i j p hp
  have hy:∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ y w:=by
    filter_upwards [hreg,(source_holomorphic i j p hp).filter_mono nhdsWithin_le_nhds] with w hr hg
    exact (PELOriginalGluedCoordinatesHolomorphy318.along_holomorphic_curve i g w hg hr).2.differentiableAt
  have hcoord:∀ᶠ w in 𝓝[≠] (0:ℂ),(coordinates i (g w)).1=a+w^2:=by
    filter_upwards [hreg,(source_projection i j p hp).filter_mono nhdsWithin_le_nhds] with w hr hpw
    exact OnePoint.coe_injective ((coordinates_projection i (g w) hr).trans hpw)
  have he:∀ᶠ w in 𝓝[≠] (0:ℂ),y w^2=polynomial l (a+w^2):=by
    filter_upwards [hreg,hcoord] with w hr hc
    have hh:=coordinates_equation i (g w) hr
    rw [hc] at hh
    exact hh
  obtain ⟨q,k,hq,hq0,hqd,hk,hk0,hl,hr,hqs,hA,hpoint⟩:=
    LegendrePuncturedFiniteExtension318.extend l h0 h1 j y hy he
  have hpun:∀ᶠ w in 𝓝[≠] (0:ℂ),completedMap i (g w)=
      some (LegendreLiteralFiniteBranch318.point l h0 h1 j (q w)):=by
    filter_upwards [hreg,hcoord,hpoint] with w hgw hcw hpw
    rw [show completedMap i (g w)=some (finiteMap i ⟨g w,hgw⟩) from
      completedMap_regular i ⟨g w,hgw⟩]
    apply congrArg some
    apply Subtype.ext
    change coordinates i (g w)=_
    rw [hpw]
    exact Prod.ext hcw rfl
  have hcenter:completedMap i (g 0)=some (LegendreLiteralFiniteBranch318.point l h0 h1 j (q 0)):=by
    rw [show g 0=p from source_zero i j p hp,hq0]
    apply completedMap_branch i p
    · rw [hp]
      fin_cases j <;> simp [Branch,branch]
    · change ((branch l j+(0:ℂ)^2:ℂ):OnePoint ℂ)=normalizedMap i p
      simpa only [zero_pow (by decide:2≠0),add_zero] using hp.symm
  refine ⟨q,k,hq,hq0,hqd,hk,hk0,hl,hr,hqs,hA,?_⟩
  have hh:=eventually_nhdsWithin_iff.mp hpun
  filter_upwards [hh] with w hw
  by_cases hz:w=0
  · simpa only [hz] using hcenter
  · exact hw hz
end PELOriginalFiniteBranchExtension318
