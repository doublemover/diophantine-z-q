module
public import PELOriginalRegularLegendreHomeomorph318
public import PELOriginalLiteralBranchParameters318
public import LegendreLiteralFiniteBranch318
public section
noncomputable section
namespace PELOriginalFiniteBranchSource318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRegularCoverPatches318
open LegendreSimpleBranchCharts318 LegendreHalfPlaneAnalyticSheets318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

@[expose] def parameter (j:Fin 3) (p:CharacterBase i)
    (hp:normalizedMap i p=(branch (branchParameter i) j:OnePoint ℂ)) :=
  PELOriginalLiteralBranchParameters318.finite i p (branch (branchParameter i) j) hp
    (by fin_cases j <;> simp [branch])
@[expose] def source (j:Fin 3) (p:CharacterBase i)
    (hp:normalizedMap i p=(branch (branchParameter i) j:OnePoint ℂ)) : ℂ→CharacterBase i:=
  fun w=>(parameter i j p hp).chart.symm ((parameter i j p hp).inverseChange w)
lemma source_zero (j:Fin 3) (p:CharacterBase i)
    (hp:normalizedMap i p=(branch (branchParameter i) j:OnePoint ℂ)) : source i j p hp 0=p := by
  let P:=parameter i j p hp
  change P.chart.symm (P.inverseChange 0)=p
  rw [P.inverse_zero,←P.center_zero]
  exact P.chart.left_inv P.center_mem
lemma source_holomorphic (j:Fin 3) (p:CharacterBase i)
    (hp:normalizedMap i p=(branch (branchParameter i) j:OnePoint ℂ)) :
    ∀ᶠ w in 𝓝 (0:ℂ),ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (source i j p hp) w := by
  let P:=parameter i j p hp
  filter_upwards [P.projection,P.inverse_analytic.eventually_analyticAt] with w hw ha
  exact (P.chart_inverse_holomorphic _ hw.1).comp w
    (contMDiffAt_iff_contDiffAt.mpr ha.contDiffAt)
lemma source_projection (j:Fin 3) (p:CharacterBase i)
    (hp:normalizedMap i p=(branch (branchParameter i) j:OnePoint ℂ)) :
    ∀ᶠ w in 𝓝 (0:ℂ),normalizedMap i (source i j p hp w)=
      (branch (branchParameter i) j+w^2:ℂ) :=
  (parameter i j p hp).projection.mono fun _ hw=>hw.2

/-- All sufficiently small NONZERO parameters lie in the actual whole
regular cover locus. This is derived from the original simple cubic
factor, not assumed from informal local branch multiplicity. -/
lemma source_regular (j:Fin 3) (p:CharacterBase i)
    (hp:normalizedMap i p=(branch (branchParameter i) j:OnePoint ℂ)) :
    ∀ᶠ w in 𝓝[≠] (0:ℂ),source i j p hp w∈Regular i := by
  let l:=branchParameter i
  let a:=branch l j
  have hc:LegendreLiteralFiniteBranch318.cofactor l j a≠0:=by
    rw [LegendreLiteralFiniteBranch318.cofactor_center]
    exact branch_slope_nonzero l (branchParameter_nonexceptional i).1
      (branchParameter_nonexceptional i).2 j
  have htc:ContinuousAt (fun w:ℂ=>LegendreLiteralFiniteBranch318.cofactor l j (a+w^2)) 0:=by
    have ht:ContinuousAt (fun w:ℂ=>a+w^2) 0:=by fun_prop
    have hh:ContinuousAt (LegendreLiteralFiniteBranch318.cofactor l j) (a+(0:ℂ)^2):=
      (LegendreLiteralFiniteBranch318.cofactor_analytic l j _).continuousAt
    exact hh.comp ht
  have hn:∀ᶠ w in 𝓝 (0:ℂ),LegendreLiteralFiniteBranch318.cofactor l j (a+w^2)≠0:=
    htc.eventually_ne (by simpa using hc)
  filter_upwards [source_projection i j p hp |>.filter_mono nhdsWithin_le_nhds,
    hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hu hne
  have hpoly:polynomial l (a+w^2)≠0:=by
    rw [LegendreLiteralFiniteBranch318.factorization l (a+w^2) j]
    change ((a+w^2)-a)*LegendreLiteralFiniteBranch318.cofactor l j (a+w^2)≠0
    rw [add_sub_cancel_left]
    exact mul_ne_zero (pow_ne_zero 2 hne) hu
  refine ⟨a+w^2,hw,?_,?_,?_⟩
  all_goals
    intro h
    apply hpoly
    simp [polynomial,h]
end PELOriginalFiniteBranchSource318
