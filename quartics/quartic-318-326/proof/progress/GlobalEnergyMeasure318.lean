module
public import HolomorphicEnergy318
public import Mathlib.MeasureTheory.Measure.WithDensity
public section
noncomputable section
open Set MeasureTheory Metric
namespace GlobalEnergyMeasure318
set_option maxHeartbeats 0

/-- A chart coordinate expression of an actual global differential energy
measure. Its local total mass is computed from the measure equality; no local
energy bound is supplied. -/
theorem chart_energy_mass {X:Type*} [MeasurableSpace X]
    (mu:Measure X) (U:Set X) (q:X→ℂ) (t:Set ℂ) (f:ℂ→ℂ)
    (hq:AEMeasurable q (mu.restrict U))
    (hchart:Measure.map q (mu.restrict U)=
      (volume.restrict t).withDensity (fun w=>ENNReal.ofReal (‖f w‖^2))) :
    (∫⁻w in t,ENNReal.ofReal (‖f w‖^2))=mu U := by
  have hh:=congrArg (fun nu:Measure ℂ=>nu univ) hchart
  rw [Measure.map_apply_of_aemeasurable hq MeasurableSet.univ,
    withDensity_apply _ MeasurableSet.univ] at hh
  simpa only [Set.preimage_univ,Measure.restrict_apply_univ,Measure.restrict_univ] using hh.symm

/-- Normalization of the global energy measure implies both integrability
and ordinary local area energy at most one in the actual chart. The density
identity is the differential-coordinate interpretation, not an inequality. -/
theorem normalized_chart_energy {X:Type*} [MeasurableSpace X]
    (mu:Measure X) (U:Set X) (q:X→ℂ) (t:Set ℂ) (f:ℂ→ℂ)
    (hq:AEMeasurable q (mu.restrict U)) (hmu:mu univ≤1)
    (hchart:Measure.map q (mu.restrict U)=
      (volume.restrict t).withDensity (fun w=>ENNReal.ofReal (‖f w‖^2)))
    (hf:AEStronglyMeasurable (fun w=>‖f w‖^2) (volume.restrict t)) :
    IntegrableOn (fun w=>‖f w‖^2) t ∧ (∫w in t,‖f w‖^2)≤1 := by
  have hmass:=chart_energy_mass mu U q t f hq hchart
  have hl : (∫⁻w in t,ENNReal.ofReal (‖f w‖^2))≤1 := by
    rw [hmass]
    exact (measure_mono (Set.subset_univ U)).trans hmu
  have hn : 0≤ᵐ[volume.restrict t] (fun w=>‖f w‖^2) :=
    Filter.Eventually.of_forall (fun w=>sq_nonneg ‖f w‖)
  have hi : IntegrableOn (fun w=>‖f w‖^2) t := by
    exact ⟨hf,(hasFiniteIntegral_iff_ofReal hn).mpr (hl.trans_lt (by simp))⟩
  refine ⟨hi,?_⟩
  have he:=ofReal_integral_eq_lintegral_ofReal hi hn
  rw [←he] at hl
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ)≤1)).mp (by simpa using hl)

/-- Holomorphic chart transitions preserve the already normalized global
energy and supply the complete local Wronskian energy input. -/
theorem normalized_pullback_energy {X:Type*} [MeasurableSpace X]
    (mu:Measure X) (U:Set X) (q:X→ℂ) (t:Set ℂ) (f F:ℂ→ℂ) (c:ℂ) (rho:ℝ)
    (hq:AEMeasurable q (mu.restrict U)) (hmu:mu univ≤1)
    (hchart:Measure.map q (mu.restrict U)=
      (volume.restrict t).withDensity (fun w=>ENNReal.ofReal (‖f w‖^2)))
    (hf:AEStronglyMeasurable (fun w=>‖f w‖^2) (volume.restrict t))
    (hF:DifferentiableOn ℂ F (ball c rho)) (hinj:InjOn F (ball c rho))
    (himage:F '' ball c rho ⊆ t) :
    IntegrableOn (fun z=>‖f (F z)*deriv F z‖^2) (ball c rho) ∧
      (∫z in ball c rho,‖f (F z)*deriv F z‖^2)≤1 := by
  obtain ⟨hi,he⟩:=normalized_chart_energy mu U q t f hq hmu hchart hf
  exact HolomorphicEnergy318.pullback_energy_one F f c rho t hF hinj himage hi he

end GlobalEnergyMeasure318
#print axioms GlobalEnergyMeasure318.chart_energy_mass
#print axioms GlobalEnergyMeasure318.normalized_chart_energy
#print axioms GlobalEnergyMeasure318.normalized_pullback_energy
