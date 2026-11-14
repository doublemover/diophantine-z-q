module
public import ActualModFourLFunctionBoundary318
public section
noncomputable section
namespace ActualCorrectionUniformBounds318
open scoped BigOperators Topology
open Filter ActualSieveEulerProduct318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def partialCorrection (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N : ℕ) : ℝ :=
  ∏ p∈Finset.range N,factor κ γ j₀ p
lemma partial_positive (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ) :
    0<partialCorrection κ γ j₀ N :=
  Finset.prod_pos (fun p _ => factor_positive κ hκ γ hγ j₀ j₁ h0 h1 p)

/-- Uniform upper control of the ACTUAL partial correction products,
constructed from the earlier absolutely convergent positive product.
Small cutoffs are included by an explicit finite positive sum. -/
theorem actual_uniform_upper (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ U : ℝ,0<U ∧ ∀ N,partialCorrection κ γ j₀ N≤U := by
  obtain ⟨C,hC,hprod⟩ := positive_product κ hκ γ hγ j₀ j₁ h0 h1
  have ht : Tendsto (partialCorrection κ γ j₀) atTop (𝓝 C) := hprod.tendsto_prod_nat
  have he : ∀ᶠ N : ℕ in atTop,partialCorrection κ γ j₀ N<C+1 :=
    ht.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  let A : ℝ := ∑ n∈Finset.range N₀,partialCorrection κ γ j₀ n
  have hA : 0≤A := Finset.sum_nonneg (fun n _ =>
    (partial_positive κ hκ γ hγ j₀ j₁ h0 h1 n).le)
  refine ⟨C+1+A,by linarith,?_⟩
  intro N
  by_cases hn : N₀≤N
  · have hh := hN₀ N hn
    linarith
  · have hm : N∈Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hh : partialCorrection κ γ j₀ N≤A := Finset.single_le_sum
      (fun n _ => (partial_positive κ hκ γ hγ j₀ j₁ h0 h1 n).le) hm
    linarith

end ActualCorrectionUniformBounds318
