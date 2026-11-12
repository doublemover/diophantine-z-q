module
public import OriginalPeriodNativeLocalInverses318
public section
noncomputable section
namespace OriginalPeriodIndependentGraphComparison318
open OriginalComplexPeriodPair318 OriginalPeriodIndependentGraphs318
open OriginalPeriodNativeLocalInverses318 ComplexAffineFreeTranslation318 Filter
open scoped Topology
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Independent target graph uniqueness identifies the ACTUAL original
finite analytic coordinates, on a whole original parameter neighborhood.
The target graph was constructed from the scheme equation, not transported. -/
theorem finite_comparison (z : ℂ) (hz : z∉(pair L).lattice) :
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g (nativeX L z) ∧ g (nativeX L z)=nativeY L z ∧
      (∀ᶠ v in 𝓝 (nativeX L z,nativeY L z),finiteEquation L v=0 ↔ g v.1=v.2) ∧
      (∀ᶠ w in 𝓝 z,g (nativeX L w)=nativeY L w)) ∨
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g (nativeY L z) ∧ g (nativeY L z)=nativeX L z ∧
      (∀ᶠ v in 𝓝 (nativeX L z,nativeY L z),finiteEquation L v=0 ↔ g v.2=v.1) ∧
      (∀ᶠ w in 𝓝 z,g (nativeY L w)=nativeX L w)) := by
  have ht : Tendsto (fun w => (nativeX L w,nativeY L w)) (𝓝 z)
      (𝓝 (nativeX L z,nativeY L z)) :=
    ((nativeX_analytic L z hz).continuousAt.prodMk (nativeY_analytic L z hz).continuousAt).tendsto
  have ho := (pair L).isClosed_lattice.isOpen_compl.mem_nhds hz
  rcases finite_graph L (nativeX L z,nativeY L z) (equation L z hz) with
    ⟨g,hg,hval,he,hu⟩ | ⟨g,hg,hval,he,hu⟩
  · left
    refine ⟨g,hg,hval,hu,?_⟩
    filter_upwards [ht.eventually hu,ho] with w hw hwl
    exact hw.mp (equation L w hwl)
  · right
    refine ⟨g,hg,hval,hu,?_⟩
    filter_upwards [ht.eventually hu,ho] with w hw hwl
    exact hw.mp (equation L w hwl)

/-- The independent actual infinity graph agrees with BOTH native
regularized coordinates through the pole, rather than only off it. -/
theorem infinity_comparison : ∃ g : ℂ → ℂ,AnalyticAt ℂ g 0 ∧ g 0=0 ∧
    (∀ᶠ v in 𝓝 ((0,0):ℂ × ℂ),infinityEquation L v=0 ↔ g v.1=v.2) ∧
    (∀ᶠ z in 𝓝 (0:ℂ),g (2*WeierstrassInfinityChart318.u (pair L) z)=
      2*WeierstrassInfinityChart318.v (pair L) z) := by
  obtain ⟨g,hg,hval,he,hu⟩ := infinity_graph L
  refine ⟨g,hg,hval,hu,?_⟩
  have hc : ContinuousAt (fun z : ℂ =>
      (2*WeierstrassInfinityChart318.u (pair L) z,2*WeierstrassInfinityChart318.v (pair L) z)) 0 := by
    exact (continuousAt_const.mul (WeierstrassInfinityChart318.u_analytic (pair L)).continuousAt).prodMk
      (continuousAt_const.mul (WeierstrassInfinityChart318.v_analytic (pair L)).continuousAt)
  have ht : Tendsto (fun z : ℂ =>
      (2*WeierstrassInfinityChart318.u (pair L) z,2*WeierstrassInfinityChart318.v (pair L) z))
      (𝓝 (0:ℂ)) (𝓝 ((0,0):ℂ × ℂ)) := by
    simpa only [WeierstrassInfinityChart318.u_zero,WeierstrassInfinityChart318.v_zero,mul_zero]
      using hc.tendsto
  filter_upwards [ht.eventually hu,WeierstrassInfinityChart318.cubic_eventually (pair L)] with z hz hc
  apply hz.mp
  dsimp [infinityEquation,OriginalPeriodProjectiveModel318.A,OriginalPeriodProjectiveModel318.B]
  linear_combination 2*hc
end OriginalPeriodIndependentGraphComparison318
