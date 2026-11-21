module

public import SelectedActualAbelIdentityChartLifts318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homeomorph.Defs

public section

noncomputable section

open Filter Function Set Topology
open scoped Topology

namespace SelectedActualAbelSameExponentialLatticeQuotient318

open SelectedActualAbelIdentityChartLifts318

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]

/-- A neighborhood of zero on which the *given* exponential is
injective. This is a kernel-isolation statement, not a new torus. -/
theorem exists_open_local_injectivity (q : V →+ J) (chart : IdentityChart q) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧ Set.InjOn q U := by
  let G : V → V := fun x => chart.coord (q x)
  have hG : HasStrictFDerivAt G (ContinuousLinearEquiv.refl ℂ V : V →L[ℂ] V) (0 : V) :=
    chart.exp_deriv
  let e : OpenPartialHomeomorph V V := hG.toOpenPartialHomeomorph G
  have he : (e : V → V) = G := hG.toOpenPartialHomeomorph_coe
  refine ⟨e.source,e.open_source,hG.mem_toOpenPartialHomeomorph_source,?_⟩
  intro x hx y hy h
  have hcoord : e x = e y :=
    (congrFun he x).trans ((congrArg chart.coord h).trans (congrFun he y).symm)
  exact (e.left_inv hx).symm.trans ((congrArg (fun w => e.symm w) hcoord).trans (e.left_inv hy))

/-- The actual exponential is open, proved from the fixed normalized
analytic chart and continuity, without assuming a quotient topology
on the given target. -/
theorem actual_exponential_isOpenMap (q : V →+ J) (hq : Continuous q)
    (chart : IdentityChart q) : IsOpenMap q := by
  let G : V → V := fun x => chart.coord (q x)
  have hG : HasStrictFDerivAt G (ContinuousLinearEquiv.refl ℂ V : V →L[ℂ] V) (0 : V) :=
    chart.exp_deriv
  let e : OpenPartialHomeomorph V V := hG.toOpenPartialHomeomorph G
  have he : (e : V → V) = G := hG.toOpenPartialHomeomorph_coe
  have hG₀ : G 0 = 0 := by
    change chart.coord (q 0) = 0
    rw [map_zero,chart.coord_zero]
  have he₀ : e 0 = 0 := (congrFun he 0).trans hG₀
  have hes : (0 : V) ∈ e.source := hG.mem_toOpenPartialHomeomorph_source
  have het : (0 : V) ∈ e.target := he₀ ▸ e.map_source hes
  have hlog₀ : e.symm 0 = 0 :=
    (congrArg (fun w : V => e.symm w) he₀.symm).trans (e.left_inv hes)
  have hcoord : ContinuousAt chart.coord (0 : J) :=
    chart.coord_cont.continuousAt (chart.source_open.mem_nhds chart.zero_mem)
  have hC : ContinuousAt (fun y : J => e.symm (chart.coord y)) 0 := by
    have hs : ContinuousAt (e.symm : V → V) (chart.coord 0) := by
      rw [chart.coord_zero]
      exact e.continuousAt_symm het
    exact ContinuousAt.comp (f := chart.coord) hs hcoord
  have hC₀ : e.symm (chart.coord 0) = 0 := by rw [chart.coord_zero,hlog₀]
  have hqC : ContinuousAt (fun y : J => q (e.symm (chart.coord y))) 0 :=
    ContinuousAt.comp (f := fun y : J => e.symm (chart.coord y)) hq.continuousAt hC
  have hqC₀ : q (e.symm (chart.coord 0)) = 0 := by rw [hC₀,map_zero]
  have hTn : e.target ∈ 𝓝 (chart.coord 0) := by
    rw [chart.coord_zero]
    exact e.open_target.mem_nhds het
  have hT : ∀ᶠ y in 𝓝 (0 : J), chart.coord y ∈ e.target :=
    hcoord.eventually hTn
  have hAtn : chart.source ∈ 𝓝 (q (e.symm (chart.coord 0))) := by
    rw [hqC₀]
    exact chart.source_open.mem_nhds chart.zero_mem
  have hAt : ∀ᶠ y in 𝓝 (0 : J), q (e.symm (chart.coord y)) ∈ chart.source :=
    hqC.eventually hAtn
  apply (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := q)).mpr
  intro W hW
  let U : Set V := (q : V → J) ⁻¹' W
  have hU : U ∈ 𝓝 (0 : V) := hW
  have hUn : U ∈ 𝓝 (e.symm (chart.coord 0)) := by
    rw [hC₀]
    exact hU
  have hW' : ∀ᶠ y in 𝓝 (0 : J), e.symm (chart.coord y) ∈ U :=
    hC.eventually hUn
  change W ∈ 𝓝 (0 : J)
  filter_upwards [hW',hT,chart.source_open.eventually_mem chart.zero_mem,hAt] with y hy hT hS hA
  have hh : chart.coord (q (e.symm (chart.coord y))) = chart.coord y :=
    (congrFun he (e.symm (chart.coord y))).symm.trans (e.right_inv hT)
  have hy' : q (e.symm (chart.coord y)) = y := chart.coord_inj hA hS hh
  change q (e.symm (chart.coord y)) ∈ W at hy
  exact hy' ▸ hy

/-- Quotient by the actual kernel of the same exponential. The result
identifies every quotient representative with its original image in J.
To use an independently constructed integral period lattice L, supply
the exact equality L = ker q, not merely finite index or real span. -/
theorem same_exponential_lattice_quotient (q : V →+ J) (hq : Continuous q)
    (hqS : Surjective q) (chart : IdentityChart q)
    (L : AddSubgroup V) (hL : L = q.ker) :
    ∃ H : (V ⧸ L) ≃ₜ J, ∀ x : V, H (QuotientAddGroup.mk x) = q x := by
  subst L
  let e : (V ⧸ q.ker) ≃+ J := QuotientAddGroup.quotientKerEquivOfSurjective q hqS
  let Q : V → V ⧸ q.ker := QuotientAddGroup.mk
  have hQ : IsQuotientMap Q := QuotientAddGroup.isQuotientMap_mk q.ker
  have hev (x : V) : e (Q x) = q x := by
    change QuotientAddGroup.kerLift q (QuotientAddGroup.mk x) = q x
    exact QuotientAddGroup.kerLift_mk q x
  have hcomp : (e : (V ⧸ q.ker) → J) ∘ Q = q := funext hev
  have hec : Continuous (e : (V ⧸ q.ker) → J) := by
    apply hQ.continuous_iff.mpr
    rw [hcomp]
    exact hq
  have hqo : IsOpenMap q := actual_exponential_isOpenMap q hq chart
  have heo : IsOpenMap (e : (V ⧸ q.ker) → J) := by
    intro U hU
    have hset : (e : (V ⧸ q.ker) → J) '' U = (q : V → J) '' (Q ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        obtain ⟨x,hx⟩ := hQ.surjective z
        refine ⟨x,?_,(hev x).symm.trans (congrArg e hx)⟩
        change Q x ∈ U
        rw [hx]
        exact hz
      · rintro ⟨x,hx,rfl⟩
        exact ⟨Q x,hx,hev x⟩
    rw [hset]
    exact hqo _ (hQ.continuous.isOpen_preimage _ hU)
  refine ⟨e.toEquiv.toHomeomorphOfContinuousOpen hec heo,?_⟩
  intro x
  exact (congrFun (Equiv.toHomeomorphOfContinuousOpen_apply e.toEquiv hec heo) (Q x)).trans (hev x)

end SelectedActualAbelSameExponentialLatticeQuotient318

#print axioms SelectedActualAbelSameExponentialLatticeQuotient318.exists_open_local_injectivity
#print axioms SelectedActualAbelSameExponentialLatticeQuotient318.actual_exponential_isOpenMap
#print axioms SelectedActualAbelSameExponentialLatticeQuotient318.same_exponential_lattice_quotient
