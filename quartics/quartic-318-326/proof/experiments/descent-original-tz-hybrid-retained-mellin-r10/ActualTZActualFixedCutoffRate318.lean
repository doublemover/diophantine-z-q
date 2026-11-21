module
public import ActualTZLiteralContextBounds318
public import ActualTZLiteralWindowEventual318
import all ActualTZLiteralContextBounds318
public section
noncomputable section
namespace ActualTZActualFixedCutoffRate318
open MeasureTheory Filter
open scoped BigOperators Topology
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZSharedXDivisorAverage318
open ActualTZLiteralOrdinaryBound318 ActualTZLiteralOrdinaryCorrection318 ActualTZLiteralContextBounds318
open ActualTZOrdinaryBoundaryScalar318 ActualTZOrdinaryBoundaryDecay318
open ActualTZOrdinaryNumericDensity318 ActualTZOrdinaryLeadingDecay318 ActualTZOrdinaryCollisionCutoffRate318
open ActualTZLiteralWindowEventual318
open ActualTZLiteralSchwartz318 ActualTZAngularKernelMain318 ActualTZAngularTensorTail318
open ActualTZLiteralMellinTensor318

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def kernelSize (C : Cutoff) (I : Type*) [Fintype I] [DecidableEq I] : ℝ :=
  2*(∫ ξ,‖mainDensity C ξ‖ ∂μ I)

theorem kernel_nonneg (C : Cutoff) : 0≤kernelSize C I :=
  mul_nonneg (by norm_num) (integral_nonneg (fun _=>norm_nonneg _))

/-- Actual ordinary estimate with the correct fixed-cutoff order
on each fixed shape. The scale factor d(y)>0 can vary arbitrarily
with the already fixed wheel. Later terminal coefficients and
the marker are not fixed before N, but their size constant is. -/
theorem rate (C : Cutoff) (hχ : (∫ t in (0:ℝ)..1,|deriv C.χ t|^2)=1)
    (B A ρ : ℝ) (hB : ∀ t,|C.χ t|≤B) (hρ : 0<ρ) (c : ℕ)
    (hsmall : 8*(Fintype.card I:ℝ)*ρ<1) :
    ∃ e : ℕ→ℝ,Tendsto e atTop (𝓝 0) ∧ (∀ y,0≤e y) ∧
    ∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∀ d>0,∃ N₀ : ℕ,∀ N≥N₀,
      ∀ {S : ActualTZJointPolynomialForms318.Terminal m a b}
        (X : Context (j:=j) S I),scales X y N c d→marker X A→
      |original X (α (primorial y)) ((X.n:ℝ)^ρ) C.χ-1|≤e y+ε := by
  let k := Fintype.card I
  let L := gridConstant I m a j c
  let Z := kernelSize C I
  have hZ : 0≤Z := kernel_nonneg C
  let e (y : ℕ) := Z*|leading k A L y|
  have hLeading : Tendsto (leading k A L) atTop (𝓝 0) := leading_tendsto _ _ _
  have he : Tendsto e atTop (𝓝 0) := by
    have H := (tendsto_const_nhds : Tendsto (fun _ : ℕ=>Z) atTop (𝓝 Z)).mul hLeading.abs
    simpa only [e,abs_zero,mul_zero] using H
  obtain ⟨y₀,hyOne,hy₀⟩ := fixed_cutoff k A L (gridConstant_nonneg (I:=I) (m:=m) (a:=a) (j:=j) c)
  refine ⟨e,he,fun _=>mul_nonneg hZ (abs_nonneg _),y₀,?_⟩
  intro y hy ε hε d hd
  have hW : 0<primorial y := primorial_pos _
  have hε₃ : 0<ε/3 := by positivity
  have hεZ : 0<ε/(3*(1+Z)) := by positivity
  obtain ⟨N₁,hN₁⟩ := hy₀ y hy _ hεZ d hd
  obtain ⟨L₀,hLone,hLit⟩ := literal_bound (m:=m) (a:=a) (b:=b) (j:=j) (I:=I) C hχ B hB y
    (ε/3) hε₃
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp ((logarithmic_growth (primorial y) hW ρ hρ).eventually_ge_atTop L₀)
  let Q := keyCount I c*(1+charge I m a j/d)
  have hNat := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop).comp
    (natural_growth (primorial y) hW)
  have hD := (total_tendsto k ρ B Q hsmall).comp hNat
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp (hD.eventually (gt_mem_nhds hε₃))
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN S X hX hK
  have hNA : N₁≤N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNB : N₂≤N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNC : N₃≤N := (le_max_right _ _).trans hN
  let R := (X.n:ℝ)^ρ
  have hlog : L₀≤Real.log R := by unfold R; rw [hX.2.2.1]; exact hN₂ _ hNB
  have hR : 1<R := by
    by_contra hr
    have hr' : R≤1 := le_of_not_gt hr
    have hR₀ : (0:ℝ)<R := Real.rpow_pos_of_pos (by exact_mod_cast X.npos) _
    have hh : Real.log R≤0 := by simpa only [Real.log_one] using Real.log_le_log hR₀ hr'
    linarith only [hlog,hLone,hh]
  obtain ⟨K,hKpos,hKsize,hKlocal⟩ := hK
  have hyX := hX.1
  obtain ⟨P,_,_,_,H⟩ := hLit X hyX R hR hlog K hKlocal
  have hMarker : Real.log K≤A*(y:ℝ) := by simpa only [hyX] using hKsize
  have hCorrection := hN₁ N hNA (primorial y) (P+1) K hKpos
    (fun p hp hp'=>hp.dvd_primorial_iff.2 hp') hMarker (X.M:ℝ) hX.2.2.2.2
  have hEuler : correctionBudget X (P+1) K≤leading k A L y+ε/(3*(1+Z)) := by
    rw [correction_as X y N c (P+1) K d hX]
    exact hCorrection
  have hτ := α_bounds (primorial y) hW
  have hB₀ := (abs_nonneg _).trans (hB 0)
  have hBoundary := three_boundary_terms X y N c d ρ (α (primorial y)) B hd hX hR hτ.1 hτ.2 hB₀
  have hBoundary' : envelope k R B*lostBound X+
      intervalError X (α (primorial y)) R B+lostBound X≤remainder k ρ B Q (X.n:ℝ) := hBoundary
  have hBsmall : remainder k ρ B Q (X.n:ℝ)≤ε/3 := by
    rw [hX.2.2.1]
    exact (hN₃ N hNC).le
  have hEuler' := mul_le_mul_of_nonneg_left hEuler hZ
  have hTail : Z*(ε/(3*(1+Z)))≤ε/3 := by
    have hu : Z/(1+Z)≤1 := (div_le_one (by positivity : 0<1+Z)).2 (by linarith)
    have H := mul_le_mul_of_nonneg_right hu (show 0≤ε/3 by positivity)
    calc
      _ = (Z/(1+Z))*(ε/3) := by
        have hu' : 0<1+Z := by positivity
        field_simp [hu'.ne'] <;> ring
      _ ≤ _ := by simpa only [one_mul] using H
  have hAbs := mul_le_mul_of_nonneg_left (le_abs_self (leading k A L y)) hZ
  change |original X (α (primorial y)) R C.χ-1|≤_
  change _ ≤ envelope k R B*lostBound X+intervalError X (α (primorial y)) R B+
    Z*correctionBudget X (P+1) K+ε/3+lostBound X at H
  change _ ≤ Z*|leading k A L y|+ε
  nlinarith only [H,hBoundary',hBsmall,hEuler',hTail,hAbs]

end ActualTZActualFixedCutoffRate318
