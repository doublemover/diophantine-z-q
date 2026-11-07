module
public import ActualCuspHomeomorph318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318 QuotientJ318 HighQParameter318 ActualCuspHomeomorph318
open HolomorphicCharts318
open scoped Manifold ContDiff
namespace HolomorphicCuspChart318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def coordinateFunction (N:ℕ) (b:Base (image N)) : ℂ :=
  ReciprocalCuspCoordinate318.inverseGerm ((jMap N b)⁻¹)

theorem coordinateFunction_projection (N:ℕ) (tau:UpperHalfPlane) (htau:tau∈high height) :
    coordinateFunction N (quotientMap N tau)=Periodic.qParam 1 tau := recovery tau htau

theorem coordinateFunction_holomorphic (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (coordinateFunction N) (neighborhood N height) := by
  letI:=complexChartedSpace N hN
  intro b hb
  obtain ⟨tau,htau,rfl⟩:=hb
  apply ContMDiffAt.contMDiffWithinAt
  let e := (quotient_localHomeomorph N hN).localInverseAt tau
  have hq:quotientMap N tau∈e.source :=
    (quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source
  have he:ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e (quotientMap N tau) :=
    (HolomorphicInverse318.localInverseAt_holomorphic N hN tau _ hq).contMDiffAt
      (e.open_source.mem_nhds hq)
  have hqf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun tau:UpperHalfPlane=>Periodic.qParam 1 tau) :=
    (Periodic.contDiff_qParam (h:=1) ω).contMDiff.comp UpperHalfPlane.contMDiff_coe
  have hc := (hqf (e (quotientMap N tau))).comp (quotientMap N tau) he
  apply hc.congr_of_eventuallyEq
  have hh : ∀ᶠb in 𝓝 (quotientMap N tau),e b∈high height := by
    apply he.continuousAt.eventually
    apply (high_open height).mem_nhds
    simpa only [e,(quotient_localHomeomorph N hN).localInverseAt_apply_self] using htau
  filter_upwards [e.open_source.mem_nhds hq,hh] with b hb hh
  have hp:quotientMap N (e b)=b :=
    (quotient_localHomeomorph N hN).apply_localInverseAt_of_mem hb
  exact (congrArg (coordinateFunction N) hp).symm.trans
    (coordinateFunction_projection N (e b) hh)

/-- The genuine homeomorphism's forward coordinate is exactly this proved
holomorphic function on the actual open quotient neighborhood. -/
theorem cuspHomeomorph_coordinate (N:ℕ) (b:neighborhood N height) :
    (cuspHomeomorph N b:ℂ)=coordinateFunction N b := rfl

end HolomorphicCuspChart318
