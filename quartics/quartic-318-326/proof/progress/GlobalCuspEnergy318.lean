module
public import CuspArakelovData318
public import GlobalEnergyMeasure318
public section
noncomputable section
namespace GlobalCuspEnergy318
open NumberField MeasureTheory Metric Set Function
set_option maxHeartbeats 0
variable (K X : Type*) [Field K] [NumberField K] [MeasurableSpace X]

/-- Actual global differential-energy data in each cusp chart.  The global
space may be a disjoint union of the complex fibers.  Only mass normalization
and the exact chart-density identity are supplied, not local integrability or
local energy inequalities. -/
structure Data (g i N : ℕ) where
  G : ℂ → ℂ
  holomorphicG : ∀ z, ‖z‖ ≤ (1 : ℝ) / 100 → DifferentiableAt ℂ G z
  boundG : ∀ z, ‖z‖ ≤ (1 : ℝ) / 100 → ‖G z‖ ≤ 128
  zeroG : G 0 = 1
  width : (K →+* ℂ) → ℕ
  width_pos : ∀ sigma, 1 ≤ width sigma
  width_level : ∀ sigma, width sigma ≤ N
  tau : (K →+* ℂ) → UpperHalfPlane
  fundamental : ∀ sigma, Real.sqrt 3 / 2 ≤ (tau sigma).im
  selected_value : ∀ sigma, G (Periodic.qParam 1 (tau sigma)) =
    Periodic.qParam 1 (tau sigma) * (1728 * ((2 : ℂ)^128 + i))
  f : (K →+* ℂ) → Fin g → ℂ → ℂ
  holomorphic : ∀ sigma j, DifferentiableOn ℂ (f sigma j)
    (ball (Periodic.qParam (width sigma) (tau sigma)) (CuspRadius318.radius (width sigma)))
  mu : (K →+* ℂ) → Fin g → Measure X
  region : (K →+* ℂ) → Set X
  coordinate : (K →+* ℂ) → X → ℂ
  coordinate_measurable : ∀ sigma j,
    AEMeasurable (coordinate sigma) ((mu sigma j).restrict (region sigma))
  mass : ∀ sigma j, mu sigma j univ ≤ 1
  chart_density : ∀ sigma j,
    Measure.map (coordinate sigma) ((mu sigma j).restrict (region sigma)) =
      (volume.restrict (ball (Periodic.qParam (width sigma) (tau sigma))
        (CuspRadius318.radius (width sigma)))).withDensity
          (fun z => ENNReal.ofReal (‖f sigma j z‖^2))
  nonWeierstrass : ∀ sigma, WronskianFinite318.wronskian g (f sigma)
    (Periodic.qParam (width sigma) (tau sigma)) ≠ 0

variable {K X}

/-- Local energy and integrability are consequences of actual global mass
and chart transport, for every complex embedding and every differential. -/
theorem Data.local_energy {g i N : ℕ} (D : Data K X g i N)
    (sigma : K →+* ℂ) (j : Fin g) :
    IntegrableOn (fun z : ℂ => ‖D.f sigma j z‖^2)
      (ball (Periodic.qParam (D.width sigma) (D.tau sigma))
        (CuspRadius318.radius (D.width sigma))) ∧
    (∫ z in ball (Periodic.qParam (D.width sigma) (D.tau sigma))
      (CuspRadius318.radius (D.width sigma)), ‖D.f sigma j z‖^2) ≤ 1 := by
  exact GlobalEnergyMeasure318.normalized_chart_energy
    (D.mu sigma j) (D.region sigma) (D.coordinate sigma) _ (D.f sigma j)
    (D.coordinate_measurable sigma j) (D.mass sigma j) (D.chart_density sigma j)
    (((D.holomorphic sigma j).continuousOn.norm.pow 2).aestronglyMeasurable
      isOpen_ball.measurableSet)

/-- Genuine constructor for the frozen cusp/Arakelov data.  Neither local
energy nor integrability is an input to this constructor. -/
@[expose] def Data.toCusp {g i N : ℕ} (D : Data K X g i N) :
    CuspArakelovData318.Data K g i N where
  G := D.G
  holomorphicG := D.holomorphicG
  boundG := D.boundG
  zeroG := D.zeroG
  width := D.width
  width_pos := D.width_pos
  width_level := D.width_level
  tau := D.tau
  fundamental := D.fundamental
  selected_value := D.selected_value
  f := D.f
  holomorphic := D.holomorphic
  integrable := fun sigma j => (D.local_energy sigma j).1
  energy := fun sigma j => (D.local_energy sigma j).2
  nonWeierstrass := D.nonWeierstrass

/-- The averaged actual derivative and Wronskian bounds now use global
normalized measures, with no supplied local norm bound. -/
theorem Data.actual_archimedean_bounds {g i N : ℕ} (D : Data K X g i N)
    (hg : 2 ≤ g) (hi : i ≤ g^3 + 1) (hN : 1 ≤ N) :
    -CuspArakelovData318.embeddingAverage K D.toCusp.differentialLog ≤
      absLogHeight₁ (1 / ((2 : ℚ)^128 + i)) + 9 ∧
    CuspArakelovData318.embeddingAverage K D.toCusp.wronskianLog ≤
      100 * (g : ℝ)^2 * Real.log (2 * g * N) :=
  CuspArakelovData318.actual_archimedean_bounds D.toCusp hg hi hN

end GlobalCuspEnergy318
#print axioms GlobalCuspEnergy318.Data.local_energy
#print axioms GlobalCuspEnergy318.Data.toCusp
#print axioms GlobalCuspEnergy318.Data.actual_archimedean_bounds
