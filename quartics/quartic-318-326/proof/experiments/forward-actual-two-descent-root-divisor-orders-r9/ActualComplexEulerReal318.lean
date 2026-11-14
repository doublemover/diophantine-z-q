module
public import ActualCharacterFiniteLogControl318
public section
noncomputable section
namespace ActualComplexEulerReal318
open scoped BigOperators Topology
open Filter ActualModFourSieveCharacter318 ActualModFourLFunctionBoundary318
open ActualCharacterFiniteLogControl318
set_option maxHeartbeats 18000000

lemma original_complex_factor (σ : ℝ) (p : ℕ) :
    (1-complexCharacter (p:ZMod 4)*(p:ℂ)^(-(σ:ℂ)))⁻¹=
      ((1-realCharacter p*(p:ℝ)^(-σ))⁻¹:ℝ) := by
  have hp : (p:ℂ)^(-(σ:ℂ))=((p:ℝ)^(-σ):ℂ) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_natCast] using
      (Complex.ofReal_cpow (Nat.cast_nonneg p) (-σ)).symm
  rw [complex_character_value,hp]
  simp only [Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]

lemma original_complex_product (σ : ℝ) (S : Finset ℕ) :
    (∏p∈S,(1-complexCharacter (p:ZMod 4)*(p:ℂ)^(-(σ:ℂ)))⁻¹)=
      (finiteEuler σ S:ℂ) := by
  rw [finiteEuler,Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun p _ => original_complex_factor σ p)

/-- The genuine complex Dirichlet Euler limit becomes the limit of
these SAME positive real products, hence the norm of the actual L-value. -/
theorem actual_real_euler_limit (σ : ℝ) (hσ : 1<σ) :
    Tendsto (fun M : ℕ => finiteEuler σ (Nat.primesBelow M)) atTop
      (𝓝 ‖DirichletCharacter.LFunction complexCharacter (σ:ℂ)‖) := by
  have ht := (actual_euler_limit σ hσ).norm
  have he (M : ℕ) : ‖∏p∈Nat.primesBelow M,
      (1-complexCharacter (p:ZMod 4)*(p:ℂ)^(-(σ:ℂ)))⁻¹‖=
        finiteEuler σ (Nat.primesBelow M) := by
    rw [original_complex_product,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_pos (finite_euler_pos σ hσ.le _ (fun p hp => Nat.prime_of_mem_primesBelow hp))
  simpa only [he] using ht

end ActualComplexEulerReal318
