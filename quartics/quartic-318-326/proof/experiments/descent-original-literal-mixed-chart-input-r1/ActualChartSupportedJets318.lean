module
public import ActualOrderedChartJets318
public import ActualTubeChartPoissonInput318
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import all ActualPureChartAxes318
public section
noncomputable section
namespace ActualChartSupportedJets318

open MeasureTheory Set
open scoped ContDiff Topology
open AffineThreePoissonRows318 ActualTubeChartPoissonInput318
open DominatedScalarIntegralJets318 ActualPureChartAxes318 ActualOrderedChartJets318

private theorem phase_continuous : Continuous phase :=
  continuous_subtype_val.comp Real.continuous_fourierChar

private theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := Circle.norm_coe _

/-- The same compact integration-variable box supports every derivative.
The bound is one scalar per order; it is not a Fourier-decay assumption. -/
theorem jet_of_compact {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (hm : MeasurableSet K)
    (F : ℕ → ℝ → E → ℂ)
    (hc : ∀ n s, Continuous (F n s))
    (hz : ∀ n s p, p ∉ K → F n s p = 0)
    (hd : ∀ n s p, HasDerivAt (fun t => F n t p) (F (n+1) s p) s)
    (hb : ∀ n, ∃ C : ℝ, ∀ s p, ‖F n s p‖ ≤ C) : Jet μ F where
  integral n s := by
    apply (hc n s).integrable_of_hasCompactSupport
    change IsCompact (closure (Function.support (F n s)))
    have he : Function.support (F n s) ⊆ K := by
      intro p hp
      by_contra hp'
      exact hp (hz n s p hp')
    exact hK.of_isClosed_subset isClosed_closure
      (closure_minimal he hK.isClosed)
  deriv := hd
  bound n := by
    obtain ⟨C,hC⟩ := hb (n+1)
    refine ⟨K.indicator (fun _ => C), ?_, ?_⟩
    · exact (integrableOn_const (μ := μ) (C := C) hK.measure_ne_top).integrable_indicator hm
    · intro s p
      by_cases hp : p ∈ K
      · rw [indicator_of_mem hp]
        exact hC s p
      · rw [indicator_of_notMem hp,hz _ _ _ hp,norm_zero]

@[expose] def Tjet (κ τ X : ℝ) (i : Fin 4) (n : ℕ) (x y z : ℝ) : ℂ :=
  steps .t n (actual κ τ i) (X,x,y,z)

@[expose] def Vjet (κ τ X : ℝ) (i : Fin 4) (n : ℕ) (x y z : ℝ) : ℂ :=
  steps .v n (actual κ τ i) (X,x,y,z)

theorem Tjet_eq (κ τ X : ℝ) (i : Fin 4) (n : ℕ) (x y z : ℝ) :
    DY (W κ τ i X) n x y z = Tjet κ τ X i n x y z :=
  congrFun (iterated_line .t X (z,x) (actual_contDiff κ τ i) n) y

theorem Vjet_eq (κ τ X : ℝ) (i : Fin 4) (n : ℕ) (x y z : ℝ) :
    DZ (W κ τ i X) n x y z = Vjet κ τ X i n x y z :=
  congrFun (iterated_line .v X (y,x) (actual_contDiff κ τ i) n) z

theorem Tjet_deriv (κ τ X : ℝ) (i : Fin 4) (n : ℕ) (x y z : ℝ) :
    HasDerivAt (fun s => Tjet κ τ X i n x s z) (Tjet κ τ X i (n+1) x y z) y :=
  step_line .t X (z,x) y (steps_smooth .t (actual_contDiff κ τ i) n)

theorem Vjet_deriv (κ τ X : ℝ) (i : Fin 4) (n : ℕ) (x y z : ℝ) :
    HasDerivAt (fun s => Vjet κ τ X i n x y s) (Vjet κ τ X i (n+1) x y z) z :=
  step_line .v X (y,x) z (steps_smooth .v (actual_contDiff κ τ i) n)

private theorem left_const_deriv {f : ℝ → ℂ} {s : ℝ} {d : ℂ}
    (c : ℂ) (h : HasDerivAt f d s) :
    HasDerivAt (fun t => c*f t) (c*d) s := h.const_mul c

/-- One genuine limit interchange for the exact first partial transform:
differentiate the physical T row while integrating physical Z. -/
theorem actual_yjet (κ τ X : ℝ) (i : Fin 4) (hτ : 0 < τ) (ξ z : ℝ) :
    Jet (volume : Measure ℝ) (Ykernel (W κ τ i X) ξ z) := by
  let K : Set ℝ := Icc (-4) 4
  apply jet_of_compact volume (K := K) isCompact_Icc measurableSet_Icc
  · intro n y
    simp only [Ykernel,Tjet_eq,Tjet]
    exact (phase_continuous.comp (by fun_prop : Continuous (fun x : ℝ => -(x*ξ)))).mul
      ((steps_smooth .t (actual_contDiff κ τ i) n).continuous.comp
        (by fun_prop : Continuous (fun x : ℝ => (X,x,y,z))))
  · intro n y x hx
    have hx' : ¬ |x| ≤ 4 := fun hu => hx (mem_symmetric.mpr hu)
    have hu : (X,x,y,z) ∉ fullBox τ := fun h => hx' (mem_symmetric.mp h.2.1)
    have he : Tjet κ τ X i n x y z = 0 :=
      actual_ordered_outside κ τ i .z .t 0 n hτ hu
    simp only [Ykernel,Tjet_eq,he,mul_zero]
  · intro n y x
    simpa only [Ykernel,Tjet_eq] using
      left_const_deriv (phase (-(x*ξ))) (Tjet_deriv κ τ X i n x y z)
  · intro n
    obtain ⟨C,_,hC⟩ := actual_ordered_uniform κ τ i .z .t 0 n hτ
    refine ⟨C,?_⟩
    intro y x
    simpa only [Ykernel,Tjet_eq,Tjet,norm_mul,phase_norm,one_mul] using hC (X,x,y,z)

/-- Integrate physical (T,Z) in that order, and differentiate physical V.
Both fixed frequency factors have norm one. -/
theorem actual_zjet (κ τ X : ℝ) (i : Fin 4) (hτ : 0 < τ) (ξ η : ℝ) :
    Jet ((volume : Measure ℝ).prod volume) (Zkernel (W κ τ i X) ξ η) := by
  let K : Set ℝ := Icc (-4) 4
  apply jet_of_compact ((volume : Measure ℝ).prod volume) (K := K ×ˢ K)
    (isCompact_Icc.prod isCompact_Icc) (measurableSet_Icc.prod measurableSet_Icc)
  · intro n z
    simp only [Zkernel,Vjet_eq,Vjet]
    exact (phase_continuous.comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => -(p.1*η)))).mul
      ((phase_continuous.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => -(p.2*ξ)))).mul
        ((steps_smooth .v (actual_contDiff κ τ i) n).continuous.comp
          (by fun_prop : Continuous (fun p : ℝ × ℝ => (X,p.2,p.1,z)))))
  · intro n z p hp
    have hu : (X,p.2,p.1,z) ∉ fullBox τ := fun h =>
      hp ⟨h.2.2.1,h.2.1⟩
    have he : Vjet κ τ X i n p.2 p.1 z = 0 :=
      actual_ordered_outside κ τ i .z .v 0 n hτ hu
    simp only [Zkernel,Vjet_eq,he,mul_zero]
  · intro n z p
    simpa only [Zkernel,Vjet_eq] using left_const_deriv (phase (-(p.1*η)))
      (left_const_deriv (phase (-(p.2*ξ))) (Vjet_deriv κ τ X i n p.2 p.1 z))
  · intro n
    obtain ⟨C,_,hC⟩ := actual_ordered_uniform κ τ i .z .v 0 n hτ
    refine ⟨C,?_⟩
    intro z p
    simpa only [Zkernel,Vjet_eq,Vjet,norm_mul,phase_norm,one_mul] using hC (X,p.2,p.1,z)

end ActualChartSupportedJets318
