module
public import GlobalEnergyMeasure318
public import ActualWronskian318
public section
noncomputable section
open Set MeasureTheory Metric
namespace ChartWronskian318
set_option maxHeartbeats 0

/-- The actual pullback coefficient of the differential f(w)dw. -/
@[expose] def pullback (F f:ℂ→ℂ) : ℂ→ℂ := fun z=>f (F z)*deriv F z

theorem pullback_holomorphic (F f:ℂ→ℂ) (s t:Set ℂ) (hs:IsOpen s)
    (hF:DifferentiableOn ℂ F s) (hf:DifferentiableOn ℂ f t)
    (himage:F '' s ⊆ t) : DifferentiableOn ℂ (pullback F f) s := by
  exact (hf.comp hF (fun z hz=>himage ⟨z,hz,rfl⟩)).mul (hF.deriv hs)

/-- A coefficient bound obtained from global image-region energy by genuine
holomorphic pullback, not from an assumed local energy inequality. -/
theorem coefficient_from_global_energy (F f:ℂ→ℂ) (c:ℂ) (rho:ℝ) (t:Set ℂ)
    (hrho:0<rho) (hF:DifferentiableOn ℂ F (ball c rho))
    (hinj:InjOn F (ball c rho)) (hf:DifferentiableOn ℂ f t)
    (himage:F '' ball c rho ⊆ t)
    (hfi:IntegrableOn (fun w=>‖f w‖^2) t) (hglobal:(∫w in t,‖f w‖^2)≤1) (j:ℕ) :
    ‖iteratedDeriv j (pullback F f) c/(j.factorial:ℂ)‖ ≤
      Real.sqrt ((j+1:ℝ)/Real.pi)*(rho⁻¹)^(j+1) := by
  obtain ⟨hi,he⟩ := HolomorphicEnergy318.pullback_energy_one F f c rho t hF hinj himage hfi hglobal
  exact ActualWronskian318.local_coefficient (pullback F f) c rho hrho
    (pullback_holomorphic F f _ _ isOpen_ball hF hf himage) hi he j

/-- All differential energies and coordinate coefficients are transported by
one actual injective holomorphic chart before taking the factorial Wronskian. -/
theorem wronskian_from_global_energy (g:ℕ) (hg:1≤g) (N rho:ℝ) (hN:1≤N)
    (hrho:Real.exp (-21)/N≤rho) (F:ℂ→ℂ) (f:Fin g→ℂ→ℂ) (c:ℂ) (t:Set ℂ)
    (hF:DifferentiableOn ℂ F (ball c rho)) (hinj:InjOn F (ball c rho))
    (hf:∀i,DifferentiableOn ℂ (f i) t) (himage:F '' ball c rho ⊆ t)
    (hfi:∀i,IntegrableOn (fun w=>‖f i w‖^2) t)
    (hglobal:∀i,(∫w in t,‖f i w‖^2)≤1) :
    Real.log ‖WronskianFinite318.wronskian g (fun i=>pullback F (f i)) c‖ ≤
      100*(g:ℝ)^2*Real.log (2*g*N) := by
  have he (i:Fin g) := HolomorphicEnergy318.pullback_energy_one F (f i) c rho t
    hF hinj himage (hfi i) (hglobal i)
  exact ActualWronskian318.local_wronskian_bound g hg N rho hN hrho
    (fun i=>pullback F (f i)) c
    (fun i=>pullback_holomorphic F (f i) _ _ isOpen_ball hF (hf i) himage)
    (fun i=>(he i).1) (fun i=>(he i).2)

/-- Wronskian bound from normalized actual global energy measures and their
chart density identities. No local energy bound or integrability is assumed. -/
theorem wronskian_from_global_measure {X:Type*} [MeasurableSpace X]
    (g:ℕ) (hg:1≤g) (N rho:ℝ) (hN:1≤N) (hrho:Real.exp (-21)/N≤rho)
    (mu:Fin g→Measure X) (U:Set X) (q:X→ℂ) (t:Set ℂ) (ht:IsOpen t)
    (F:ℂ→ℂ) (f:Fin g→ℂ→ℂ) (c:ℂ)
    (hq:∀i,AEMeasurable q ((mu i).restrict U)) (hmu:∀i,mu i univ≤1)
    (hchart:∀i,Measure.map q ((mu i).restrict U)=
      (volume.restrict t).withDensity (fun w=>ENNReal.ofReal (‖f i w‖^2)))
    (hF:DifferentiableOn ℂ F (ball c rho)) (hinj:InjOn F (ball c rho))
    (hf:∀i,DifferentiableOn ℂ (f i) t) (himage:F '' ball c rho ⊆ t) :
    Real.log ‖WronskianFinite318.wronskian g (fun i=>pullback F (f i)) c‖ ≤
      100*(g:ℝ)^2*Real.log (2*g*N) := by
  have he (i:Fin g) := GlobalEnergyMeasure318.normalized_chart_energy
    (mu i) U q t (f i) (hq i) (hmu i) (hchart i)
    (((hf i).continuousOn.norm.pow 2).aestronglyMeasurable ht.measurableSet)
  exact wronskian_from_global_energy g hg N rho hN hrho F f c t hF hinj hf himage
    (fun i=>(he i).1) (fun i=>(he i).2)

end ChartWronskian318
#print axioms ChartWronskian318.pullback_holomorphic
#print axioms ChartWronskian318.coefficient_from_global_energy
#print axioms ChartWronskian318.wronskian_from_global_energy

#print axioms ChartWronskian318.wronskian_from_global_measure
