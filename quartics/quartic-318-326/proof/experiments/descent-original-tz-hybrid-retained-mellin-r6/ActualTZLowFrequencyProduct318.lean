module
public import ActualTZLowFrequencyPole318
public import ActualTZFiniteProductNearOne318
public section
noncomputable section
namespace ActualTZLowFrequencyProduct318
open scoped BigOperators
open ActualTZLowFrequencyPole318 ActualTZMellinKernel318 ActualTZZetaPoleRatio318
open ActualTZFiniteProductNearOne318

/-- No inverse ζ bound on growing imaginary lines. This exact
normalized finite-vector relative estimate holds concurrently in
every literal low-band angular variable. -/
theorem normalized_product {I : Type*} [Fintype I] (ε : ℝ) (hε : 0<ε) (hε' : ε≤1/2) :
    ∃ L₀≥(1:ℝ),∀ L≥L₀,∀ ξ η : I→ℝ,
      (∀ i,|ξ i|≤band L) → (∀ i,|η i|≤band L) →
      ‖(∏ i : I,(L:ℂ)*ratio (shift L (ξ i)) (shift L (η i)))-
        (∏ i : I,kernel (ξ i) (η i))‖≤
      ‖∏ i : I,kernel (ξ i) (η i)‖*(Real.exp (14*(Fintype.card I:ℝ)*ε)-1) := by
  obtain ⟨L₀,h₀,H⟩ := correction_uniform ε hε hε'
  refine ⟨L₀,h₀,?_⟩
  intro L hL ξ η hξ hη
  have hp := zero_lt_one.trans_le (h₀.trans hL)
  simp_rw [scaled_zeta_identity L _ _ hp,Finset.prod_mul_distrib]
  let K := ∏ i : I,kernel (ξ i) (η i)
  let P := ∏ i : I,ActualTZLowFrequencyPole318.correction L (ξ i) (η i)
  change ‖K*P-K‖≤_
  have hKP : K*P-K=K*(P-1) := by ring
  have hB : ‖P-1‖≤Real.exp (14*(Fintype.card I:ℝ)*ε)-1 := by
    have H₁ := product_near_one (Finset.univ : Finset I)
      (fun i => ActualTZLowFrequencyPole318.correction L (ξ i) (η i)) (fun _ => 14*ε)
      (fun i _ => H L hL (ξ i) (η i) (hξ i) (hη i))
    simpa only [P,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      mul_assoc,mul_comm,mul_left_comm] using H₁
  rw [hKP,norm_mul]
  exact mul_le_mul_of_nonneg_left hB (norm_nonneg K)

end ActualTZLowFrequencyProduct318
