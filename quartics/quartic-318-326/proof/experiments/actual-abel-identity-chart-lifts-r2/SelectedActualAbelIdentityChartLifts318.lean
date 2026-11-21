module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Group.Basic

public section

noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace SelectedActualAbelIdentityChartLifts318

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]

/-- One normalized identity chart of the given actual Jacobian, in
the frame fixed by its invariant differentials. The coefficient space
of q is its actual tangent space in that frame. -/
structure IdentityChart (q : V →+ J) where
  coord : J → V
  source : Set J
  source_open : IsOpen source
  zero_mem : (0 : J) ∈ source
  coord_zero : coord 0 = 0
  coord_cont : ContinuousOn coord source
  coord_inj : Set.InjOn coord source
  exp_deriv : HasStrictFDerivAt (fun x => coord (q x))
    (ContinuousLinearEquiv.refl ℂ V : V →L[ℂ] V) (0 : V)

/-- Build the coordinate lift into the given actual exponential on a
whole disk. The readout of the original invariant derivative is given
before choosing a logarithm, by the centered chart at each source point.
No inverse, period-zero equality or independent target is assumed.

To prove the derivative of the single constructed lift at every point
of the disk, compare its increments to the same identity inverse,
now centered at that point. -/
theorem exists_disk_lift
    (q : V →+ J) (hq : Continuous q) (hqS : Surjective q)
    (chart : IdentityChart q)
    (a : ℂ → J) (U : Set ℂ) (hU : IsOpen U) (ha : ContinuousOn a U)
    (v : ℂ → V)
    (hread : ∀ z ∈ U, HasDerivAt (fun w => chart.coord (a w - a z)) (v z) z)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ U ∧ ∃ lift : ℂ → V,
      (∀ z ∈ ball z₀ r, q (lift z) = a z) ∧
      (∀ z ∈ ball z₀ r, HasDerivAt lift (v z) z) := by
  let G : V → V := fun x => chart.coord (q x)
  have hG : HasStrictFDerivAt G (ContinuousLinearEquiv.refl ℂ V : V →L[ℂ] V) (0 : V) :=
    chart.exp_deriv
  let e : OpenPartialHomeomorph V V := hG.toOpenPartialHomeomorph G
  have he : (e : V → V) = G := hG.toOpenPartialHomeomorph_coe
  have hG₀ : G 0 = 0 := by
    change chart.coord (q 0) = 0
    rw [map_zero, chart.coord_zero]
  have he₀ : e 0 = 0 := (congrFun he 0).trans hG₀
  have hes : (0 : V) ∈ e.source := hG.mem_toOpenPartialHomeomorph_source
  have het : (0 : V) ∈ e.target := he₀ ▸ e.map_source hes
  have hlog₀ : e.symm 0 = 0 :=
    (congrArg (fun w : V => e.symm w) he₀.symm).trans (e.left_inv hes)
  have hlog : HasFDerivAt (e.symm : V → V) (ContinuousLinearMap.id ℂ V) (0 : V) := by
    have h := hG.to_localInverse.hasFDerivAt
    change HasFDerivAt (e.symm : V → V) (ContinuousLinearMap.id ℂ V) (G 0) at h
    exact hG₀ ▸ h
  obtain ⟨x₀,hx₀⟩ := hqS (a z₀)
  let c (w : ℂ) : V := chart.coord (a w - a z₀)
  let L (w : ℂ) : V := e.symm (c w) + x₀
  have hc₀ : c z₀ = 0 := by
    change chart.coord (a z₀ - a z₀) = 0
    rw [sub_self,chart.coord_zero]
  have hc : ContinuousAt c z₀ := (hread z₀ hz₀).continuousAt
  have hcT : ∀ᶠ w in 𝓝 z₀, c w ∈ e.target :=
    hc.eventually (hc₀.symm ▸ e.open_target.eventually_mem het)
  have hA₀ : a z₀ - a z₀ ∈ chart.source := by
    rw [sub_self]
    exact chart.zero_mem
  have hA : ∀ᶠ w in 𝓝 z₀, a w - a z₀ ∈ chart.source :=
    ((ha.continuousAt (hU.mem_nhds hz₀)).sub continuousAt_const).eventually
      (chart.source_open.eventually_mem hA₀)
  have hC₀ : ContinuousAt (fun w => e.symm (c w)) z₀ := by
    have hC : ContinuousAt (e.symm : V → V) (c z₀) := by
      rw [hc₀]
      exact e.continuousAt_symm het
    exact hC.comp hc
  have hQC₀ : q (e.symm (c z₀)) = 0 := by rw [hc₀,hlog₀,map_zero]
  have hQcont : ContinuousAt (fun w : ℂ => q (e.symm (c w))) z₀ :=
    hq.continuousAt.comp hC₀
  have hQN : chart.source ∈ 𝓝 (q (e.symm (c z₀))) := by
    rw [hQC₀]
    exact chart.source_open.mem_nhds chart.zero_mem
  have hQC : ∀ᶠ w in 𝓝 z₀, q (e.symm (c w)) ∈ chart.source :=
    hQcont.eventually hQN
  have hgood : ∀ᶠ w in 𝓝 z₀,
      w ∈ U ∧ c w ∈ e.target ∧ a w - a z₀ ∈ chart.source ∧
        q (e.symm (c w)) ∈ chart.source := by
    filter_upwards [hU.eventually_mem hz₀,hcT,hA,hQC] with w hw h₁ h₂ h₃
    exact ⟨hw,h₁,h₂,h₃⟩
  obtain ⟨r,hr,hB⟩ := Metric.mem_nhds_iff.mp hgood
  let B : Set ℂ := ball z₀ r
  have hBU : B ⊆ U := fun z hz => (hB hz).1
  have val (w : ℂ) (hw : w ∈ B) : q (L w) = a w := by
    obtain ⟨_,hT,hA,hQ⟩ := hB hw
    have hb : chart.coord (q (e.symm (c w))) = chart.coord (a w - a z₀) :=
      (congrFun he (e.symm (c w))).symm.trans (e.right_inv hT)
    have hx := chart.coord_inj hQ hA hb
    change q (e.symm (c w) + x₀) = a w
    rw [map_add,hx,hx₀,sub_add_cancel]
  refine ⟨r,hr,hBU,L,val,?_⟩
  intro z hz
  have haz := ha.continuousAt (hU.mem_nhds (hBU hz))
  have hsub : ContinuousAt (fun w : ℂ => a w - a z₀) z :=
    haz.sub continuousAt_const
  have hchart_z : ContinuousAt chart.coord (a z - a z₀) :=
    chart.coord_cont.continuousAt (chart.source_open.mem_nhds (hB hz).2.2.1)
  have hc_z : ContinuousAt c z := hchart_z.comp hsub
  have hLz : ContinuousAt L z :=
    ((e.continuousAt_symm (hB hz).2.1).comp hc_z).add continuousAt_const
  have hInc₀ : L z - L z = 0 := sub_self _
  have hIcont : ContinuousAt (fun w : ℂ => L w - L z) z :=
    hLz.sub continuousAt_const
  have hIN : e.source ∈ 𝓝 (L z - L z) := by
    rw [hInc₀]
    exact e.open_source.mem_nhds hes
  have hInc : ∀ᶠ w in 𝓝 z, L w - L z ∈ e.source :=
    hIcont.eventually hIN
  have hlift_germ : L =ᶠ[𝓝 z] (fun w => e.symm (chart.coord (a w - a z)) + L z) := by
    filter_upwards [hInc,(isOpen_ball : IsOpen B).eventually_mem hz] with w hw hBw
    have hqInc : q (L w - L z) = a w - a z := by rw [map_sub,val w hBw,val z hz]
    have hcoord : e (L w - L z) = chart.coord (a w - a z) :=
      (congrFun he (L w - L z)).trans (congrArg chart.coord hqInc)
    have hx := e.left_inv hw
    rw [hcoord] at hx
    exact ((congrArg (fun x : V => x + L z) hx).trans (sub_add_cancel (L w) (L z))).symm
  have hbase : chart.coord (a z - a z) = 0 := by rw [sub_self,chart.coord_zero]
  have hlogz : HasFDerivAt (e.symm : V → V) (ContinuousLinearMap.id ℂ V)
      (chart.coord (a z - a z)) := by rw [hbase]; exact hlog
  have hder : HasDerivAt (fun w => e.symm (chart.coord (a w - a z))) (v z) z := by
    simpa only [Function.comp_def,ContinuousLinearMap.id_apply] using
      hlogz.comp_hasDerivAt z (hread z (hBU hz))
  exact (hder.add_const (L z)).congr_of_eventuallyEq hlift_germ

end SelectedActualAbelIdentityChartLifts318

#print axioms SelectedActualAbelIdentityChartLifts318.exists_disk_lift
