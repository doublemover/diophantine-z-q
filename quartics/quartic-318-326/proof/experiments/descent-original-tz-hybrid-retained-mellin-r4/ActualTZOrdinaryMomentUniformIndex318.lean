module
public import ActualTZFiniteMainBand318
public section
noncomputable section
universe v
namespace ActualTZOrdinaryMomentUniformIndex318
open MeasureTheory Filter
open scoped BigOperators Topology
open ActualTZFiniteMainBand318 ActualTZLiteralReferenceNear318
open ActualTZLiteralLowIntegral318 ActualTZAngularTensorTail318
open ActualTZAngularKernelMain318 ActualTZAngularKernelTail318
open ActualTZThreeNearFactors318 ActualTZLiteralAbsoluteEuler318 ActualTZLowFrequencyPole318
open ActualTZLiteralMellinTensor318 ActualTZLiteralSchwartz318

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem tiny_drift (k : ℕ) (v : ℝ) (hv : 0<v) :
    ∃ x : ℝ,0<x ∧ x≤1/2 ∧
      0≤drift (Real.exp (14*(k:ℝ)*x)-1) x x ∧
      drift (Real.exp (14*(k:ℝ)*x)-1) x x < v := by
  let f (x : ℝ) := drift (Real.exp (14*(k:ℝ)*x)-1) x x
  have hc : Continuous f := by unfold f drift; fun_prop
  have h0 : f 0=0 := by simp [f,drift]
  have hc0 : ContinuousAt f (0:ℝ) := hc.continuousAt
  obtain ⟨r,hr,H⟩ := (Metric.continuousAt_iff.mp hc0) v hv
  let x := min (r/2) (1/4)
  have hx : 0<x := lt_min (by positivity) (by norm_num)
  have hxr : x<r := (min_le_left _ _).trans_lt (by linarith)
  have hC : x≤1/2 := (min_le_right _ _).trans (by norm_num)
  have hE : 0≤Real.exp (14*(k:ℝ)*x)-1 := by
    exact sub_nonneg.mpr (by simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (by positivity : 0≤14*(k:ℝ)*x))
  have hb : 0≤f x := drift_nonneg _ _ _ hE hx.le hx.le
  have hd : dist x 0 < r := by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hx] using hxr
  have hf := H hd
  rw [h0,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hb] at hf
  exact ⟨x,hx,hC,hb,hf⟩

/-- Accept the genuine weighted collision bound E for the actual
row. Once the wheel W is fixed, the reference and angular errors
can be below ANY η uniformly over all actual cells, without
requiring E→0 when y is fixed. This is the ordinary finite-main
quantifier order, not the stronger fixed-y nonlinear donor. The threshold
precedes the finite cell type J, which grows with the old physical grid. -/
theorem accepts_uniform (C : Cutoff) (W : ℕ) (hW : 0<W)
    (hχ : (∫ u in (0:ℝ)..1,|deriv C.χ u|^2)=1) (η : ℝ) (hη : 0<η) :
    ∃ L₀≥(1:ℝ),∀ R>1, L₀≤Real.log R→∀ N : ℕ,
      Real.exp ((Real.log R)^2)≤(N:ℝ)→W.primeFactors⊆Nat.primesBelow (N+1)→
      ⌊R⌋₊<N+1→∀ (J : Type v) [Fintype J] (a : J→I→ℤ) (b : J→I→ℕ), (∀ j i,W.Coprime (b j i))→
      ∀ (w : J→ℝ), (∀ j,0≤w j) → (∑ j : J,w j)≤1 →∀ E≥0,
      (∀ ξ∈fullBand I (band (Real.log R)),
        (∑ j : J,w j*‖correctionAt W N (a j) (b j) (Real.log R) ξ-1‖)≤E) →
      |∑ j : J,w j*(exactMain C W (a j) (b j) R-1)| ≤
        (2*(∫ ξ,‖mainDensity C ξ‖ ∂μ I))*E+η := by
  let K := ∫ ξ,‖mainDensity C ξ‖ ∂μ I
  have hK : 0≤K := integral_nonneg (fun _=>norm_nonneg _)
  let k := Fintype.card I
  let D := offCount I
  let d := 4*(k+D+2)
  let A := (2:ℝ)^D*(∫ ξ,moments C d ξ ∂μ I)
  have hA : 0≤A := mul_nonneg (by positivity) (integral_nonneg (moments_nonneg C d))
  let v := min 1 (η/(3*(1+K)))
  have hv : 0<v := lt_min zero_lt_one (by positivity)
  obtain ⟨x,hx,hx',hδ,hSmall⟩ := tiny_drift k v hv
  let δ := drift (Real.exp (14*(k:ℝ)*x)-1) x x
  have hδ1 : δ≤1 := hSmall.le.trans (min_le_left _ _)
  have hδK : δ*K≤η/3 := by
    have ht : δ≤η/(3*(1+K)) := hSmall.le.trans (min_le_right _ _)
    have H := (le_div_iff₀ (by positivity : 0<3*(1+K))).1 ht
    nlinarith only [H,hδ]
  obtain ⟨La,hLa,hRef⟩ := ActualTZLiteralReferenceNear318.uniform (I:=I) W hW x x x hx hx' hx hx' hx
  obtain ⟨Lt,hTail⟩ := eventually_atTop.mp
    ((main_tail_tendsto (I:=I) C).eventually (gt_mem_nhds (by positivity : 0<η/3)))
  let Le := 1+3*A/η
  refine ⟨max (max La Lt) Le,hLa.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro R hR hL N hN hWheel hP J hJ a b hU w hw hT E hE hC
  let L := Real.log R
  have hLaL : La≤L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLtL : Lt≤L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLeL : Le≤L := (le_max_right _ _).trans hL
  have hL1 : 1≤L := hLa.trans hLaL
  have hRef' (ξ : Slot I→ℝ) (hξ : ξ∈fullBand I (band L)) :
      ‖sharedReference W N L (direct ξ true) (direct ξ false)-
        sharedKernel (direct ξ true) (direct ξ false)‖≤
          ‖sharedKernel (direct ξ true) (direct ξ false)‖*δ := by
    apply hRef L hLaL N hN
    · intro i
      simpa only [direct,Real.norm_eq_abs] using hξ (i,true)
    · intro i
      simpa only [direct,Real.norm_eq_abs] using hξ (i,false)
  have H := weighted_exact_main C W N hW hWheel a b hU w hw hT R hR hP hL1 hχ δ E hδ hE hRef' hC
  have hCut : (2:ℝ)^D/L^2*(∫ ξ,moments C d ξ ∂μ I)≤η/3 := by
    have hL2 : L≤L^2 := by nlinarith
    have hLe : 3*A/η≤L := by dsimp only [Le] at hLeL; linarith
    have hA2 := (div_le_iff₀ hη).1 (hLe.trans hL2)
    have hP2 : 0<L^2 := by positivity
    calc
      _ = A/L^2 := by dsimp only [A]; ring
      _ ≤ _ := (div_le_iff₀ hP2).2 (by linarith only [hA2])
  have hEt : (1+δ)*E≤2*E := mul_le_mul_of_nonneg_right (by linarith) hE
  have hM := mul_le_mul_of_nonneg_right hEt hK
  have hT' := (hTail L hLtL).le
  refine H.trans ?_
  change (δ+(1+δ)*E)*K+(_+_) ≤ (2*K)*E+η
  nlinarith only [hδK,hCut,hM,hT']

end ActualTZOrdinaryMomentUniformIndex318
