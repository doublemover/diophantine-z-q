module
public import ActualJProper318
public import Mathlib.Topology.DiscreteSubset
public section
noncomputable section
namespace ActualJFinite318
open Function Filter Topology UpperHalfPlane
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318 QuotientJ318
open OpenJLocalComparison318
set_option maxHeartbeats 0

/-- The genuine j-function has isolated equal-value points in the upper
half-plane, by analytic identity and the actual cusp nonconstancy theorem. -/
theorem exists_isolating_open (tau : UpperHalfPlane) :
    ∃U : Set UpperHalfPlane, IsOpen U ∧ tau∈U ∧
      ∀sigma∈U, ActualQJ318.jInvariant sigma=ActualQJ318.jInvariant tau → sigma=tau := by
  have hf : AnalyticOnNhd ℂ j upperHalfPlaneSet := fun z hz => j_analyticAt ⟨z,hz⟩
  have hn : ¬∀ᶠz in 𝓝 (tau:ℂ), j z=j (tau:ℂ) := by
    intro he
    have hc := hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_halfSpace_im_gt 0).isPreconnected tau.im_pos he
    apply ActualJCusp318.j_not_constant (j (tau:ℂ))
    intro sigma
    simpa only [j,UpperHalfPlane.ofComplex_apply] using hc sigma.im_pos
  have hne := ((j_analyticAt tau).eventually_eq_or_eventually_ne
    (show AnalyticAt ℂ (fun _ => j (tau:ℂ)) (tau:ℂ) from analyticAt_const)).resolve_left hn
  have hev : ∀ᶠz in 𝓝 (tau:ℂ), z≠(tau:ℂ) → j z≠j (tau:ℂ) := by
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using eventually_nhdsWithin_iff.mp hne
  obtain ⟨V,hV,hVo,ht⟩ := mem_nhds_iff.mp hev
  refine ⟨(fun sigma:UpperHalfPlane => (sigma:ℂ)) ⁻¹' V,
    hVo.preimage continuous_coe,ht,?_⟩
  intro sigma hs he
  apply coe_injective
  by_contra hn
  apply hV hs hn
  simpa only [j,UpperHalfPlane.ofComplex_apply] using he

/-- Every actual quotient j-fiber is discrete. The proof uses the genuine
open orbit projection, so does not discard elliptic stabilizers. -/
theorem discrete_fiber (N : ℕ) (z : ℂ) : IsDiscrete ((jMap N) ⁻¹' {z}) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro q hq
  obtain ⟨tau,rfl⟩ := GammaOneAtlas318.quotient_surjective N q
  change ActualQJ318.jInvariant tau=z at hq
  obtain ⟨U,hU,ht,huniq⟩ := exists_isolating_open tau
  refine ⟨quotientMap N '' U,?_,?_⟩
  · have ho : IsOpenMap (quotientMap N) := MulAction.isOpenQuotientMap_quotientMk.isOpenMap
    exact ho U hU
  · ext q
    constructor
    · rintro ⟨⟨sigma,hs,rfl⟩,hz⟩
      change ActualQJ318.jInvariant sigma=z at hz
      have he : ActualQJ318.jInvariant sigma=ActualQJ318.jInvariant tau := hz.trans hq.symm
      rw [huniq sigma hs he]
      exact Set.mem_singleton _
    · intro he
      rcases Set.mem_singleton_iff.mp he with rfl
      exact ⟨⟨tau,ht,rfl⟩,hq⟩

/-- Actual finite fibers: compactness comes from the all-cusp extension,
and discreteness from genuine analyticity, rather than a supplied finiteness axiom. -/
theorem finite_fiber (N : ℕ) (hN : 5≤N) (z : ℂ) : ((jMap N) ⁻¹' {z}).Finite :=
  (ActualJProper318.compact_fiber N hN z).finite (discrete_fiber N z)

end ActualJFinite318
