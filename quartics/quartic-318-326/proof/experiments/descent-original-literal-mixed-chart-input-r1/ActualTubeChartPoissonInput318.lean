module
public import ActualTubeAnnulusChart318
public import ActualChartFourierFubini318
public import DominatedScalarIntegralJets318
public import ActualHybridFourierSummability318
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public section
noncomputable section
namespace ActualTubeChartPoissonInput318
open MeasureTheory
open scoped FourierTransform ContDiff SchwartzMap ENNReal
open AffineThreePoissonRows318 ActualHybridFourierSummability318
open DominatedScalarIntegralJets318 ActualChartFourierFubini318
set_option maxHeartbeats 12000000

@[expose] def W (κ τ : ℝ) (i : Fin 4) (X : ℝ) : Cube :=
  fun x y z => (ActualTubeAnnulusChart318.sectionWeight κ τ i X x y z : ℂ)

@[expose] def DY (U : Cube) (n : ℕ) : Cube :=
  fun x y z => iteratedDeriv n (fun s => U x s z) y

@[expose] def DZ (U : Cube) (n : ℕ) : Cube :=
  fun x y z => iteratedDeriv n (fun s => U x y s) z

@[expose] def Ykernel (U : Cube) (ξ z : ℝ) (n : ℕ) (y x : ℝ) : ℂ :=
  phase (-(x*ξ))*DY U n x y z

/-- The carrier is literally (y,x), the same as the Fubini donor. -/
@[expose] def Zkernel (U : Cube) (ξ η : ℝ) (n : ℕ) (z : ℝ) (p : ℝ×ℝ) : ℂ :=
  phase (-(p.1*η))*(phase (-(p.2*ξ))*DZ U n p.2 p.1 z)

/-- Transient derivative certificates for the concrete section only.
Their J₀,J₂,J₄ are the already bounded chart jet suprema, not an oracle
for partial Fourier transforms or hybrid sums. -/
structure Input (κ τ : ℝ) (i : Fin 4) (X J₀ J₂ J₄ : ℝ) where
  xrow : ℝ → ℝ → 𝓢(ℝ,ℂ)
  xrow_eq : ∀ y z, (xrow y z : ℝ→ℂ)=fun x => W κ τ i X x y z
  xrowYY : ℝ → ℝ → 𝓢(ℝ,ℂ)
  xrowYY_eq : ∀ y z, (xrowYY y z : ℝ→ℂ)=fun x => DY (W κ τ i X) 2 x y z
  yjet : ∀ ξ z, Jet volume (Ykernel (W κ τ i X) ξ z)
  zjet : ∀ ξ η, Jet ((volume : Measure ℝ).prod volume) (Zkernel (W κ τ i X) ξ η)
  yzero : ∀ x y z, 4<|y| → W κ τ i X x y z=0
  yzero₂ : ∀ x y z, 4<|y| → DY (W κ τ i X) 2 x y z=0
  zzero : ∀ x y z, 4<|z| → W κ τ i X x y z=0
  nonneg₀ : 0≤J₀
  nonneg₂ : 0≤J₂
  nonneg₄ : 0≤J₄
  L₀ : ∀ y z, (∫ x,‖xrow y z x‖)≤8*J₀
  L₂x : ∀ y z, (∫ x,‖iteratedDeriv 2 (xrow y z : ℝ→ℂ) x‖)≤8*J₂
  L₂y : ∀ y z, (∫ x,‖xrowYY y z x‖)≤8*J₂
  L₄ : ∀ y z, (∫ x,‖iteratedDeriv 2 (xrowYY y z : ℝ→ℂ) x‖)≤8*J₄

variable {κ τ X J₀ J₂ J₄ : ℝ} {i : Fin 4} (D : Input κ τ i X J₀ J₂ J₄)
local notation "U" => W κ τ i X

lemma W₁_jet (ξ z : ℝ) :
    (fun y => F₁ U ξ y z)=integrated volume (Ykernel U ξ z) 0 := by
  funext y
  rw [first_as_integral]
  simp only [integrated,Ykernel,DY,iteratedDeriv_zero]

lemma W₁_second (ξ z : ℝ) :
    iteratedDeriv 2 (fun y => F₁ U ξ y z)=integrated volume (Ykernel U ξ z) 2 := by
  rw [W₁_jet,show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,
    deriv_integrated (D.yjet ξ z) 0,deriv_integrated (D.yjet ξ z) 1]

lemma W₂_integrable (ξ η z : ℝ) :
    Integrable (weightedKernel U ξ η z) ((volume : Measure ℝ).prod volume) := by
  simpa only [weightedKernel,Zkernel,DZ,iteratedDeriv_zero] using (D.zjet ξ η).integral 0 z

lemma W₂_jet (ξ η : ℝ) :
    (fun z => F₂ U ξ η z)=integrated ((volume : Measure ℝ).prod volume) (Zkernel U ξ η) 0 := by
  funext z
  rw [second_as_product_integral U ξ η z (W₂_integrable D ξ η z)]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [show -(p.2*ξ+p.1*η)=-(p.1*η)+-(p.2*ξ) by ring,phase_add]
  simp only [Zkernel,DZ,iteratedDeriv_zero,mul_assoc]

private lemma compact_y (n : ℕ) (ξ z : ℝ) (n_ok : n=0 ∨ n=2) :
    HasCompactSupport (integrated volume (Ykernel U ξ z) n) := by
  apply support_integrated n (Set.Icc (-4) 4) isCompact_Icc
  intro y hy x
  have h : 4<|y| := by
    by_contra! hh
    exact hy (by simpa only [Set.mem_Icc,abs_le] using hh)
  rcases n_ok with rfl|rfl
  · simp [Ykernel,DY,D.yzero x y z h]
  · simp [Ykernel,D.yzero₂ x y z h]

private lemma compact_z (ξ η : ℝ) :
    HasCompactSupport (integrated ((volume : Measure ℝ).prod volume) (Zkernel U ξ η) 0) := by
  apply support_integrated 0 (Set.Icc (-4) 4) isCompact_Icc
  intro z hz p
  have h : 4<|z| := by
    by_contra! hh
    exact hz (by simpa only [Set.mem_Icc,abs_le] using hh)
  simp [Zkernel,DZ,D.zzero p.2 p.1 z h]

/-- Exact sampled rows for the real chart and the actual successive
Fourier operators. No chart-dependent oracle is in the result. -/
def chartRows (H c₁ c₂ c₃ : ℝ) : Rows U H c₁ c₂ c₃ where
  row₁ j k := D.xrow (node H c₂ j) (node H c₃ k)
  row₁_val j k := D.xrow_eq _ _
  row₂ a k := (compact_y D 0 (freq H a) (node H c₃ k) (Or.inl rfl)).toSchwartzMap
    (smooth_integrated (D.yjet (freq H a) (node H c₃ k)) 0)
  row₂_val a k := (W₁_jet (freq H a) (node H c₃ k)).symm
  row₃ a b := (compact_z D (freq H a) (freq H b)).toSchwartzMap
    (smooth_integrated (D.zjet (freq H a) (freq H b)) 0)
  row₃_val a b := (W₂_jet D (freq H a) (freq H b)).symm

private theorem schwartz_integrable_deriv (s : 𝓢(ℝ,ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (s : ℝ→ℂ)) := by
  induction n generalizing s with
  | zero => simpa only [iteratedDeriv_zero] using s.integrable
  | succ n ih =>
    have h : deriv (s:ℝ→ℂ)=((SchwartzMap.derivCLM ℝ ℂ s):ℝ→ℂ) :=
      funext (fun x => (SchwartzMap.derivCLM_apply ℝ s x).symm)
    rw [iteratedDeriv_succ',h]
    exact ih _

theorem L1_box (f : ℝ→ℂ) (hf : Integrable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖≤C)
    (hz : ∀ x, 4<|x| → f x=0) :
    (∫ x,‖f x‖)≤8*C := by
  let S : Set ℝ := Set.Icc (-4) 4
  have hm : MeasurableSet S := measurableSet_Icc
  have hfin : volume S ≠ ∞ := isCompact_Icc.measure_ne_top
  calc
    _ = ∫ x in S,‖f x‖ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have h : 4<|x| := by
        by_contra! hh
        exact hx (by simpa only [S,Set.mem_Icc,abs_le] using hh)
      rw [hz x h,norm_zero]
    _ ≤ ∫ _ in S,C :=
      setIntegral_mono_on hf.norm.integrableOn (integrableOn_const hfin) hm (fun x _ => hb x)
    _ = _ := by rw [setIntegral_const]; norm_num [S,Real.volume_real_Icc,smul_eq_mul]

@[expose] def decayFactor : ℝ := (4*Real.pi^2)⁻¹
@[expose] def C₀ (J₀ J₂ : ℝ) : ℝ := 8*(J₀+decayFactor*J₂)
@[expose] def C₂ (J₀ J₂ J₄ : ℝ) : ℝ := 8*(C₀ J₀ J₂+decayFactor*C₀ J₂ J₄)

private lemma factor_nonneg : 0≤decayFactor := by unfold decayFactor; positivity
private lemma C₀_nonneg {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : 0≤C₀ a b :=
  mul_nonneg (by norm_num) (add_nonneg ha (mul_nonneg factor_nonneg hb))
private lemma C₂_nonneg {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) : 0≤C₂ a b c :=
  mul_nonneg (by norm_num) (add_nonneg (C₀_nonneg ha hb)
    (mul_nonneg factor_nonneg (C₀_nonneg hb hc)))

lemma W₁_decay (ξ y z : ℝ) : ‖F₁ U ξ y z‖≤C₀ J₀ J₂/(1+ξ^2) := by
  let s := D.xrow y z
  have hL : (∫ x,‖s x‖)+decayFactor*(∫ x,‖iteratedDeriv 2 (s:ℝ→ℂ) x‖)≤C₀ J₀ J₂ := by
    dsimp [C₀]
    have h := add_le_add (D.L₀ y z) (mul_le_mul_of_nonneg_left (D.L₂x y z) factor_nonneg)
    exact h.trans_eq (by ring)
  simpa only [s,D.xrow_eq,F₁,decayFactor] using
    (quadratic_row_bound (s.smooth'.of_le (by simp)) (fun n _ => schwartz_integrable_deriv s n) ξ _ hL)

lemma W₁_second_decay (ξ y z : ℝ) :
    ‖iteratedDeriv 2 (fun t => F₁ U ξ t z) y‖≤C₀ J₂ J₄/(1+ξ^2) := by
  let s := D.xrowYY y z
  have hL : (∫ x,‖s x‖)+decayFactor*(∫ x,‖iteratedDeriv 2 (s:ℝ→ℂ) x‖)≤C₀ J₂ J₄ := by
    dsimp [C₀]
    have h := add_le_add (D.L₂y y z) (mul_le_mul_of_nonneg_left (D.L₄ y z) factor_nonneg)
    exact h.trans_eq (by ring)
  rw [W₁_second D ξ z]
  have hI : 𝓕 (s : ℝ→ℂ) ξ = integrated volume (Ykernel U ξ z) 2 y := by
    change 𝓕 (D.xrowYY y z : ℝ→ℂ) ξ = _
    rw [D.xrowYY_eq,Real.fourier_real_eq]
    simp only [integrated,Ykernel,phase,Circle.smul_def,smul_eq_mul]
  rw [←hI]
  exact quadratic_row_bound (s.smooth'.of_le (by simp))
    (fun n _ => schwartz_integrable_deriv s n) ξ _ hL

lemma W₂_decay (ξ η z : ℝ) :
    ‖F₂ U ξ η z‖≤C₂ J₀ J₂ J₄/(1+ξ^2)/(1+η^2) := by
  let f := fun y => F₁ U ξ y z
  let s := (compact_y D 0 ξ z (Or.inl rfl)).toSchwartzMap
    (smooth_integrated (D.yjet ξ z) 0)
  have hs : (s:ℝ→ℂ)=f := (W₁_jet ξ z).symm
  have hfi (n : ℕ) : Integrable (iteratedDeriv n f) := by
    rw [←hs]
    exact schwartz_integrable_deriv s n
  have hLf : (∫ y,‖f y‖)≤8*(C₀ J₀ J₂/(1+ξ^2)) := by
    apply L1_box f (by simpa only [iteratedDeriv_zero] using hfi 0) _
      (fun y => W₁_decay D ξ y z)
    intro y hy
    change F₁ U ξ y z=0
    rw [first_as_integral]
    simp [D.yzero _ y z hy]
  have hLd : (∫ y,‖iteratedDeriv 2 f y‖)≤8*(C₀ J₂ J₄/(1+ξ^2)) := by
    apply L1_box _ (hfi 2) _ (fun y => W₁_second_decay D ξ y z)
    intro y hy
    change iteratedDeriv 2 (fun y => F₁ U ξ y z) y=0
    rw [W₁_second D ξ z]
    simp [integrated,Ykernel,D.yzero₂ _ y z hy]
  have hC : (∫ y,‖f y‖)+decayFactor*(∫ y,‖iteratedDeriv 2 f y‖)≤C₂ J₀ J₂ J₄/(1+ξ^2) := by
    have h := add_le_add hLf (mul_le_mul_of_nonneg_left hLd factor_nonneg)
    exact h.trans_eq (by unfold C₂; ring)
  have h := quadratic_row_bound (show ContDiff ℝ 2 f by rw [←hs]; exact s.smooth'.of_le (by simp))
    (fun n _ => hfi n) η _ hC
  exact h

theorem chartSwaps (H c₁ c₂ c₃ : ℝ) (hH : 0<H) : SwapSums U H c₁ c₂ c₃ := by
  apply swap_sums_from_chart_decay hH 4 4 (C₀ J₀ J₂) (C₂ J₀ J₂ J₄)
  · exact C₀_nonneg D.nonneg₀ D.nonneg₂
  · exact C₂_nonneg D.nonneg₀ D.nonneg₂ D.nonneg₄
  · intro a b c
    by_cases hy : |node H c₂ b|≤4
    · simpa [band,hy,delta,div_eq_mul_inv] using
        W₁_decay D (freq H a) (node H c₂ b) (node H c₃ c)
    · rw [first_as_integral]
      simp [band,hy,D.yzero _ _ _ (lt_of_not_ge hy)]
  · intro a b c
    by_cases hz : |node H c₃ c|≤4
    · simpa [band,hz,delta,div_eq_mul_inv,mul_assoc] using
        W₂_decay D (freq H a) (freq H b) (node H c₃ c)
    · rw [F₂,Real.fourier_real_eq]
      have hzero (y : ℝ) : F₁ U (freq H a) y (node H c₃ c)=0 := by
        rw [first_as_integral]
        simp [D.zzero _ _ _ (lt_of_not_ge hz)]
      simp [band,hz,hzero]

theorem chart_poisson (H c₁ c₂ c₃ : ℝ) (hH : 0<H) :
    (∑' c : ℤ,∑' b : ℤ,∑' a : ℤ,A₀ U H c₁ c₂ c₃ a b c) =
      ∑' a : ℤ,∑' b : ℤ,∑' c : ℤ,A₃ U H c₁ c₂ c₃ a b c :=
  affine_three hH (chartRows D H c₁ c₂ c₃) (chartSwaps D H c₁ c₂ c₃ hH)


@[expose] def lastKernel (Q : Cube) (ξ η ζ : ℝ) (p : ℝ × (ℝ×ℝ)) : ℂ :=
  phase (-(p.1*ζ))*weightedKernel Q ξ η p.1 p.2

/-- Exact final transform in product order (z,(y,x)). Only integrability
of the actual full compact weighted kernel is external to this identity. -/
theorem W₃_product (ξ η ζ : ℝ)
    (h : Integrable (lastKernel U ξ η ζ)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))) :
    F₃ U ξ η ζ =
      ∫ p : ℝ × (ℝ×ℝ),phase (-(p.2.2*ξ+p.2.1*η+p.1*ζ))*U p.2.2 p.2.1 p.1
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
  calc
    _ = ∫ z : ℝ, phase (-(z*ζ))*F₂ U ξ η z := by
      rw [F₃,Real.fourier_real_eq] <;> simp only [phase,Circle.smul_def,smul_eq_mul]
    _ = ∫ z : ℝ, ∫ p : ℝ×ℝ,lastKernel U ξ η ζ (z,p)
          ∂((volume : Measure ℝ).prod volume) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [second_as_product_integral U ξ η z (W₂_integrable D ξ η z),
        ←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [show -(p.2*ξ+p.1*η)=-(p.1*η)+-(p.2*ξ) by ring,phase_add]
      simp only [lastKernel,weightedKernel,mul_assoc]
    _ = ∫ p : ℝ × (ℝ×ℝ),lastKernel U ξ η ζ p
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) :=
      (integral_prod (lastKernel U ξ η ζ) h).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [show -(p.2.2*ξ+p.2.1*η+p.1*ζ)=-(p.1*ζ)+(-(p.2.1*η)+-(p.2.2*ξ)) by ring,
        phase_add,phase_add]
      simp only [lastKernel,weightedKernel,mul_assoc]

end ActualTubeChartPoissonInput318
