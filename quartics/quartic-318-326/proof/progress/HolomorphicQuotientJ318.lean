module
public import QuotientJ318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open HolomorphicCharts318 QuotientJ318 Filter Topology
open scoped Manifold ContDiff
namespace HolomorphicQuotientJ318
set_option maxHeartbeats 0

/-- Exact equality with the genuine analytic j-function on any actual inverse sheet. -/
theorem jMap_localInverse (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (q:Base (image N))
    (hq:q∈((quotient_localHomeomorph N hN).localInverseAt a).source) :
    jMap N q=ActualQJ318.jInvariant ((quotient_localHomeomorph N hN).localInverseAt a q) := by
  have hp:quotientMap N ((quotient_localHomeomorph N hN).localInverseAt a q)=q :=
    (quotient_localHomeomorph N hN).apply_localInverseAt_of_mem hq
  exact (congrArg (jMap N) hp).symm

/-- The descended j-map is genuinely holomorphic for the already constructed
complex analytic manifold structure on the fine-level quotient. -/
theorem jMap_holomorphic (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (jMap N) := by
  letI:=complexChartedSpace N hN
  intro q
  obtain ⟨a,rfl⟩ := quotient_surjective N q
  let e := (quotient_localHomeomorph N hN).localInverseAt a
  have hq:quotientMap N a∈e.source :=
    (quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source
  have he:ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e (quotientMap N a) :=
    (HolomorphicInverse318.localInverseAt_holomorphic N hN a _ hq).contMDiffAt
      (e.open_source.mem_nhds hq)
  have hj := (j_holomorphic (e (quotientMap N a))).comp (quotientMap N a) he
  apply hj.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hq] with q hq
  exact jMap_localInverse N hN a q hq

theorem jMap_continuous (N:ℕ) (hN:5≤N) : Continuous (jMap N) := by
  letI:=complexChartedSpace N hN
  exact (jMap_holomorphic N hN).continuous

/-- The actual qj identity in every quotient inverse sheet. No abstract
holomorphic numerator or selected-value identity is supplied. -/
theorem local_qj (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (q:Base (image N))
    (hq:q∈((quotient_localHomeomorph N hN).localInverseAt a).source) :
    let tau := (quotient_localHomeomorph N hN).localInverseAt a q
    ActualQJ318.G (Function.Periodic.qParam 1 tau) =
      Function.Periodic.qParam 1 tau * jMap N q := by
  dsimp only
  rw [jMap_localInverse N hN a q hq]
  exact ActualQJ318.G_qParam _

/-- A selected actual elliptic model at each quotient point. A choice of lift
is used only for the model; its invariant is the canonical descended j-map. -/
@[expose] def curveAt (N:ℕ) (q:Base (image N)) : WeierstrassCurve ℂ :=
  ModularWeierstrass318.curve ((quotient_surjective N q).choose)

instance curveAt_isElliptic (N:ℕ) (q:Base (image N)) : (curveAt N q).IsElliptic :=
  ModularWeierstrass318.curve_isElliptic _

theorem curveAt_j (N:ℕ) (q:Base (image N)) :
    (curveAt N q).j=jMap N q := by
  change (ModularWeierstrass318.curve ((quotient_surjective N q).choose)).j = _
  rw [ModularWeierstrass318.curve_j]
  exact (congrArg (jMap N) (quotient_surjective N q).choose_spec)

/-- Any lift, not just the selected one, has the same genuine model invariant. -/
theorem lift_model_invariant (N:ℕ) (q:Base (image N)) (tau:UpperHalfPlane)
    (htau:quotientMap N tau=q) :
    (ModularWeierstrass318.curve tau).j=(curveAt N q).j := by
  rw [curveAt_j,ModularWeierstrass318.curve_j]
  exact congrArg (jMap N) htau

end HolomorphicQuotientJ318
