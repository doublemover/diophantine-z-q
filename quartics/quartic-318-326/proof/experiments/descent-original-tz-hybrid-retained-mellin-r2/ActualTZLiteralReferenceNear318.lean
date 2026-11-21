module
public import ActualTZThreeNearFactors318
public import ActualTZLowFrequencyProduct318
public import ActualTZReferenceZetaProduct318
public import ActualTZWheelLowBand318
public section
noncomputable section
namespace ActualTZLiteralReferenceNear318
open Filter
open scoped BigOperators Topology
open ActualTZThreeNearFactors318 ActualTZLowFrequencyPole318 ActualTZLowFrequencyProduct318
open ActualTZReferenceZetaProduct318 ActualTZWheelLowBand318 ActualTZMellinKernel318

variable {I : Type*} [Fintype I]

@[expose] def sharedReference (W N : ℕ) (L : ℝ) (ξ η : I→ℝ) : ℂ :=
  multiplier W (fun i=>shift L (ξ i)) (fun i=>shift L (η i)) *
    ((L:ℂ)^Fintype.card I*
      partial (fun i=>shift L (ξ i)) (fun i=>shift L (η i)) (N+1))

@[expose] def sharedKernel (ξ η : I→ℝ) : ℂ := ∏ i : I,kernel (ξ i) (η i)

private theorem normalized_full_eq (L : ℝ) (s t : I→ℂ) :
    (L:ℂ)^Fintype.card I*zetaRatio s t =
      ∏ i : I,(L:ℂ)*ActualTZZetaPoleRatio318.ratio (s i) (t i) := by
  simp only [zetaRatio,ActualTZZetaPoleRatio318.ratio,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ]

/-- Once W is fixed, the *same* L0 works at every literal low-band
frequency and at every N≥exp(L²) (the prime universe is N+1).
The wheel, missing reference primes, and complex pole quotient
are composed without a denominator estimate at height. -/
theorem uniform (W : ℕ) (hW : 0<W) (ε τ ω : ℝ)
    (he : 0<ε) (he' : ε≤1/2) (ht : 0<τ) (ht' : τ≤1/2) (hw : 0<ω) :
    ∃ L₀≥(1:ℝ),∀ L≥L₀,∀ N : ℕ, Real.exp (L^2)≤(N:ℝ)→∀ ξ η : I→ℝ,
      (∀ i,|ξ i|≤band L) → (∀ i,|η i|≤band L) →
      ‖sharedReference W N L ξ η-sharedKernel ξ η‖≤
        ‖sharedKernel ξ η‖*drift (Real.exp (14*(Fintype.card I:ℝ)*ε)-1) τ ω := by
  let k := Fintype.card I
  let E := Real.exp (14*(k:ℝ)*ε)-1
  have hE : 0≤E := sub_nonneg.mpr (by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (by positivity : 0≤14*(k:ℝ)*ε)))
  obtain ⟨Lp,hLp,hPole⟩ := normalized_product (I:=I) ε he he'
  obtain ⟨Lw,hLw,hWheel⟩ := fixed_wheel_uniform (I:=I) W hW ω hw
  have hT := (relative_error_tendsto k).eventually (gt_mem_nhds ht)
  obtain ⟨Lt,hTail⟩ := eventually_atTop.mp hT
  refine ⟨max (max Lp Lw) Lt,hLp.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro L hL N hN ξ η hξ hη
  have hp : Lp≤L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hwp : Lw≤L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have htp : Lt≤L := (le_max_right _ _).trans hL
  have hLpos : 0<L := zero_lt_one.trans_le (hLp.trans hp)
  let s (i : I) := shift L (ξ i)
  let t (i : I) := shift L (η i)
  have hs (i : I) : 1/L≤(s i).re := by rw [s,shift_re]
  have htt (i : I) : 1/L≤(t i).re := by rw [t,shift_re]
  let P := (L:ℂ)^k*partial s t (N+1)
  let Z := (L:ℂ)^k*zetaRatio s t
  have hZT : ‖Z-P‖≤‖P‖*τ := by
    have H := omitted_relative L hLpos N hN s t hs htt
    have hTsmall : Real.exp (7*(k:ℝ)*(L*Real.exp (-L)))-1≤τ := (hTail L htp).le
    have hMod := H.trans (mul_le_mul_of_nonneg_left hTsmall (norm_nonneg _))
    dsimp only [Z,P]
    rw [←mul_sub,norm_mul,norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hMod (norm_nonneg ((L:ℂ)^k))
  have hZK : ‖Z-sharedKernel ξ η‖≤‖sharedKernel ξ η‖*E := by
    dsimp only [Z,E,k,sharedKernel]
    rw [normalized_full_eq]
    exact hPole L hp ξ η hξ hη
  exact near_reference P Z (sharedKernel ξ η) (multiplier W s t) E τ ω hE ht.le ht' hw.le
    hZT hZK (hWheel L hwp ξ η hξ hη).le

end ActualTZLiteralReferenceNear318
