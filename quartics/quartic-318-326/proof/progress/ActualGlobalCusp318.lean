module
public import GlobalEnergyJacobian318
public import ActualQJ318
public section
noncomputable section
namespace ActualGlobalCusp318
open NumberField MeasureTheory Metric Set Function
set_option maxHeartbeats 0
variable (K X : Type*) [Field K] [NumberField K] [MeasurableSpace X]

/-- Actual geometric cusp/global differential data.  The modular regularized
function and every analytic estimate for it are constructed from Mathlib's
Eisenstein series and discriminant, rather than supplied as fields. -/
structure Data (g i N : ℕ) where
  width : (K →+* ℂ) → ℕ
  width_pos : ∀ sigma, 1 ≤ width sigma
  width_level : ∀ sigma, width sigma ≤ N
  tau : (K →+* ℂ) → UpperHalfPlane
  fundamental : ∀ sigma, Real.sqrt 3 / 2 ≤ (tau sigma).im
  selected_j : ∀ sigma, ActualQJ318.jInvariant (tau sigma) =
    1728 * ((2 : ℂ)^128 + i)
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

/-- Populate the global-energy data with the actual q*j function. -/
@[expose] def Data.toGlobal {g i N : ℕ} (D : Data K X g i N) :
    GlobalCuspEnergy318.Data K X g i N where
  G := ActualQJ318.G
  holomorphicG := ActualQJ318.cusp_G_data.1
  boundG := ActualQJ318.cusp_G_data.2.1
  zeroG := ActualQJ318.cusp_G_data.2.2
  width := D.width
  width_pos := D.width_pos
  width_level := D.width_level
  tau := D.tau
  fundamental := D.fundamental
  selected_value := fun sigma => ActualQJ318.selected_value (D.tau sigma) i (D.selected_j sigma)
  f := D.f
  holomorphic := D.holomorphic
  mu := D.mu
  region := D.region
  coordinate := D.coordinate
  coordinate_measurable := D.coordinate_measurable
  mass := D.mass
  chart_density := D.chart_density
  nonWeierstrass := D.nonWeierstrass

@[expose] def Data.toCusp {g i N : ℕ} (D : Data K X g i N) :
    CuspArakelovData318.Data K g i N := D.toGlobal.toCusp

/-- The constructor uses the actual regularized modular function literally. -/
theorem Data.actual_G {g i N : ℕ} (D : Data K X g i N) :
    D.toCusp.G = ActualQJ318.G := rfl

/-- All averaged archimedean estimates now follow from actual j-values and
normalized global differential measures, without G-estimate/local-energy inputs. -/
theorem Data.actual_archimedean_bounds {g i N : ℕ} (D : Data K X g i N)
    (hg : 2 ≤ g) (hi : i ≤ g^3 + 1) (hN : 1 ≤ N) :
    -CuspArakelovData318.embeddingAverage K D.toCusp.differentialLog ≤
      absLogHeight₁ (1 / ((2 : ℚ)^128 + i)) + 9 ∧
    CuspArakelovData318.embeddingAverage K D.toCusp.wronskianLog ≤
      100 * (g : ℝ)^2 * Real.log (2 * g * N) :=
  D.toGlobal.actual_archimedean_bounds hg hi hN

/-- Exact quadratic-log Jacobian bound with both actual modular G and global
energy inputs produced, retaining only the named geometric finite/Arakelov data. -/
theorem jacobian_quadratic
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {g i d N : ℕ} (D : Data K X g i N)
    (F : SourceJacobianBound318.FiniteData ι κ (2^128 + i) d N)
    (A : SourceNonCMHeight318.ArakelovIdentifications K D.toCusp F)
    (hg : 2 ≤ g) (hi : i ≤ g^3 + 1) (hgd : g ≤ d) (hN : 1 ≤ N) :
    A.hGR ≤ 2^11 * (d : ℝ)^2 * (Real.log (6*d*N))^2 :=
  GlobalEnergyJacobian318.jacobian_quadratic K X D.toGlobal F A hg hi hgd hN

end ActualGlobalCusp318
#print axioms ActualGlobalCusp318.Data.toGlobal
#print axioms ActualGlobalCusp318.Data.toCusp
#print axioms ActualGlobalCusp318.Data.actual_archimedean_bounds
#print axioms ActualGlobalCusp318.jacobian_quadratic
