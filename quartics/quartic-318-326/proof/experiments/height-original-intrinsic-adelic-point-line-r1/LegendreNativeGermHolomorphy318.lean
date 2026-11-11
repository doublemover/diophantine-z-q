module
public import LegendreGlobalHolomorphicDifferential318
public section
noncomputable section
namespace LegendreNativeGermHolomorphy318
open Set Filter
open scoped Topology Manifold ContDiff
open LegendrePlaneOverlap318 LegendreLiteralCompletedAtlas318
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
local instance : ChartedSpace ℂ (CompletedPlane l):=
  LegendreCompletedComplexAtlas318.chartedSpace l
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CompletedPlane l):=
  LegendreCompletedComplexAtlas318.complex_manifold l

/-- Actual native finite coordinate germs map holomorphically into the
INDEPENDENT completed target atlas. Continuity is derived from the given
analytic coordinates, not assumed from a scheme-point bijection. -/
theorem finite (g : ℂ→LegendreFiniteComplexAtlas318.Plane l) (z : ℂ)
    (hg : AnalyticAt ℂ (fun w=>(g w).val) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>finiteChart l (g w)) z := by
  let e:=LegendreCompletedComplexAtlas318.finiteChart l (g z)
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CompletedPlane l):=
    IsManifold.subset_maximalAtlas ⟨Sum.inl (g z),rfl⟩
  have hp:finiteChart l (g z)∈e.source:=
    ⟨g z,LegendreFiniteComplexAtlas318.chart_center l (g z),rfl⟩
  have hc:ContinuousAt g z:=hg.continuousAt.subtype_mk _
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hp).mpr
  refine ⟨((finite_open l).continuous.continuousAt.comp hc).continuousWithinAt,?_⟩
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>e (finiteChart l (g w))) z:=by
    rcases LegendreFiniteComplexAtlas318.chart_axis l (g z) with ha|ha
    · have hd:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.1) z:=
        contMDiffAt_iff_contDiffAt.mpr (analyticAt_fst.comp hg).contDiffAt
      convert hd using 1
      funext w
      exact (LegendreCompletedComplexAtlas318.finite_apply l (g z) (g w)).trans (ha _)
    · have hd:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.2) z:=
        contMDiffAt_iff_contDiffAt.mpr (analyticAt_snd.comp hg).contDiffAt
      convert hd using 1
      funext w
      exact (LegendreCompletedComplexAtlas318.finite_apply l (g z) (g w)).trans (ha _)
  exact hh.contMDiffWithinAt

/-- The same construction through infinity uses the actual U,V native
chart and keeps its origin. No reciprocal-coordinate cancellation drops
that point, and no target complex structure is transported. -/
theorem infinity (g : ℂ→InfinityPlane l) (z : ℂ)
    (hg : AnalyticAt ℂ (fun w=>(g w).val) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>infinityChart l (g w)) z := by
  let e:=LegendreCompletedComplexAtlas318.infinityChart l (g z)
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CompletedPlane l):=
    IsManifold.subset_maximalAtlas ⟨Sum.inr (g z),rfl⟩
  have hp:infinityChart l (g z)∈e.source:=
    ⟨g z,LegendreInfinityComplexAtlas318.chart_center l (g z),rfl⟩
  have hc:ContinuousAt g z:=hg.continuousAt.subtype_mk _
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hp).mpr
  refine ⟨((infinity_open l).continuous.continuousAt.comp hc).continuousWithinAt,?_⟩
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>e (infinityChart l (g w))) z:=by
    rcases LegendreInfinityComplexAtlas318.chart_axis l (g z) with ha|ha
    · have hd:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.1) z:=
        contMDiffAt_iff_contDiffAt.mpr (analyticAt_fst.comp hg).contDiffAt
      convert hd using 1
      funext w
      exact (LegendreCompletedComplexAtlas318.infinity_apply l (g z) (g w)).trans (ha _)
    · have hd:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w=>(g w).val.2) z:=
        contMDiffAt_iff_contDiffAt.mpr (analyticAt_snd.comp hg).contDiffAt
      convert hd using 1
      funext w
      exact (LegendreCompletedComplexAtlas318.infinity_apply l (g z) (g w)).trans (ha _)
  exact hh.contMDiffWithinAt

lemma literal_inverse_finite (p : NormalizedLegendreFieldPoints318.FinitePoints l) :
    (literalCompletedEquiv l).symm (some p)=finiteChart l ((literalFiniteEquiv l).symm p) := by
  apply (literalCompletedEquiv l).injective
  rw [Equiv.apply_symm_apply,literal_finite,Equiv.apply_symm_apply]
lemma literal_inverse_infinity :
    (literalCompletedEquiv l).symm none=infinityChart l (origin l) := by
  apply (literalCompletedEquiv l).injective
  rw [Equiv.apply_symm_apply,literal_origin]
lemma literal_infinity (q : InfinityPlane l) (hv:q.val.2≠0) :
    literalCompletedEquiv l (infinityChart l q)=some (literalFiniteEquiv l (toFinite l q)) := by
  rw [←(chart_identification l (toFinite l q) q).mpr
    ⟨toFinite_nonzero l q hv,right_inverse l q hv⟩,literal_finite]
lemma literal_infinity_coordinates (q : InfinityPlane l) (hv:q.val.2≠0) :
    (literalFiniteEquiv l (toFinite l q)).val=
      (q.val.1/q.val.2+NormalizedLegendreProjectiveModel318.shift l,1/q.val.2) := by
  rw [literalFinite_value,toFinite_value l q hv]

/-- Literal t,y analytic germs, including finite branch points, enter the
SAME native completed atlas by the actual translation x=t-shift. -/
theorem literal_finite (g : ℂ→NormalizedLegendreFieldPoints318.FinitePoints l) (z:ℂ)
    (hg:AnalyticAt ℂ (fun w=>(g w).val) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun w=>(literalCompletedEquiv l).symm (some (g w))) z := by
  have hnative:AnalyticAt ℂ (fun w=>((literalFiniteEquiv l).symm (g w)).val) z:=by
    change AnalyticAt ℂ (fun w=>((g w).val.1-NormalizedLegendreProjectiveModel318.shift l,(g w).val.2)) z
    exact ((analyticAt_fst.comp hg).sub analyticAt_const).prod (analyticAt_snd.comp hg)
  have hh:=finite l (fun w=>(literalFiniteEquiv l).symm (g w)) z hnative
  convert hh using 1
  funext w
  exact literal_inverse_finite l (g w)
end LegendreNativeGermHolomorphy318
