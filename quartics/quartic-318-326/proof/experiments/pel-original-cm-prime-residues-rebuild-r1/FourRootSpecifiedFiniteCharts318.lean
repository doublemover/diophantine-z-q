module
public import FourRootNativeGermHolomorphy318
public import ComplexCurvePartialInverse318
public section
noncomputable section
namespace FourRootSpecifiedFiniteCharts318
open Set Filter FourRootNormalizedPointCharts318
open scoped Topology Manifold ContDiff
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
local instance : TopologicalSpace (Completed b) := FourRootGluedTopology318.topology b
local instance : ChartedSpace ℂ (Completed b) := FourRootCompletedComplexAtlas318.chartedSpace b hb
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed b) := FourRootCompletedComplexAtlas318.complex_manifold b hb

/-- Any genuine finite chart with analytic ambient inverse belongs to the
INDEPENDENT completed maximal atlas. Forward holomorphy is proved from
the actual local inverse theorem, not inserted as an atlas assumption. -/
theorem lifted_maximal (e : OpenPartialHomeomorph (FinitePoints b) ℂ)
    (ha : AnalyticOnNhd ℂ (fun z => (e.symm z).val) e.target) :
    e.lift_openEmbedding (FourRootGluedTopology318.finite_openEmbedding b) ∈
      IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed b) := by
  let E := e.lift_openEmbedding (FourRootGluedTopology318.finite_openEmbedding b)
  have hi : ∀ z ∈ E.target,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω E.symm z := by
    intro z hz
    apply FourRootNativeGermHolomorphy318.finite b hb e.symm z
    · exact contMDiffAt_iff_contDiffAt.mpr ((analyticAt_fst.comp (ha z hz)).contDiffAt)
    · intro i
      exact contMDiffAt_iff_contDiffAt.mpr
        ((((ContinuousLinearMap.proj (R:=ℂ) i).analyticAt _).comp
          (analyticAt_snd.comp (ha z hz))).contDiffAt)
  apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn E).mpr
  constructor
  · intro p hp
    have hh := ComplexCurvePartialInverse318.inverse_at E.symm (E p) (E.map_source hp)
      (hi (E p) (E.map_source hp))
    rw [E.left_inv hp] at hh
    exact hh.contMDiffWithinAt
  · exact fun z hz => (hi z hz).contMDiffWithinAt

/-- The prescribed regular coordinate is t itself, rather than a
possibly different root coordinate chosen by an arbitrary chart oracle. -/
theorem exists_regular (p : FinitePoints b) (hp : ∀ i,p.val.2 i≠0) :
    ∃ e : OpenPartialHomeomorph (FinitePoints b) ℂ,p∈e.source ∧
      (∀ q,e q=q.val.1) ∧ AnalyticOnNhd ℂ (fun z => (e.symm z).val) e.target := by
  obtain ⟨Z,hZ0,hbase,hroots,hright⟩ := FourRootRegularGraph318.parametrization b p hp
  have hA : AnalyticAt ℂ (fun z => (Z z).val) p.val.1 := by
    have ht : AnalyticAt ℂ (fun z => (Z z).val.1) p.val.1 := by
      simpa only [show (fun z => (Z z).val.1)=id from funext hbase] using
        (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) p.val.1)
    exact ht.prod (AnalyticAt.pi hroots)
  exact AnalyticEmbeddedCurveChart318.exists_chart
    {q : ℂ×(Fin 4→ℂ) | ∀ i,q.2 i^2=q.1-b i} p Prod.fst continuous_fst Z hA hZ0 hbase hright

include hb in
/-- At the marked branch the prescribed coordinate is the SAME vanishing
signed root. The full original target point and three other signs persist. -/
theorem exists_branch (p : FinitePoints b) (i : Fin 4) (hp : p.val.1=b i) :
    ∃ e : OpenPartialHomeomorph (FinitePoints b) ℂ,p∈e.source ∧
      (∀ q,e q=q.val.2 i) ∧ AnalyticOnNhd ℂ (fun z => (e.symm z).val) e.target := by
  obtain ⟨Z,hZ0,hbase,hroot,hroots,hright⟩ :=
    FourRootFiniteBranchGraph318.parametrization b hb i p hp
  have hz : p.val.2 i=0 := FourRootFiniteBranchGraph318.root_zero b i p hp
  have hA : AnalyticAt ℂ (fun z => (Z z).val) 0 := by
    have ht : AnalyticAt ℂ (fun z => (Z z).val.1) 0 := by
      rw [show (fun z => (Z z).val.1)=(fun z => b i+z^2) from funext hbase]
      exact analyticAt_const.add (analyticAt_id.pow 2)
    exact ht.prod (AnalyticAt.pi hroots)
  exact AnalyticEmbeddedCurveChart318.exists_chart
    {q : ℂ×(Fin 4→ℂ) | ∀ j,q.2 j^2=q.1-b j} p (fun q => q.2 i)
    ((continuous_apply i).comp continuous_snd) Z
    (by simpa only [hz] using hA) (by simpa only [hz] using hZ0) hroot hright
end FourRootSpecifiedFiniteCharts318
