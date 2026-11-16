module
public import ActualGaussianDirichlet318
public section
noncomputable section
namespace ActualGaussianEulerModel318
open ActualGaussianDirichlet318 Filter
open scoped Topology
set_option maxHeartbeats 1000000

@[expose] def localModel (k : ℕ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  (1-(p:ℂ)^(-s))^k*(1-character (p:ℕ)*(p:ℂ)^(-s))^2
@[expose] def modelValue (k : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta s)⁻¹^k*(DirichletCharacter.LFunction character s)⁻¹^2

/-- The model has an actual Euler product on its domain of absolute
convergence, built from the same Gaussian character as the local sieve. -/
theorem model_hasProd (k : ℕ) (s : ℂ) (hs : 1<s.re) :
    HasProd (localModel k s) (modelValue k s) := by
  have hz := (riemannZeta_eulerProduct_hasProd hs).inv₀
    (riemannZeta_ne_zero_of_one_le_re hs.le)
  have hl := character.LSeries_eulerProduct_hasProd hs
  rw [←character.LFunction_eq_LSeries hs] at hl
  have hli := hl.inv₀ (value_nonzero s hs.le)
  simpa only [localModel,modelValue,inv_inv] using (hz.pow k).mul (hli.pow 2)

/-- The pole normalization is an exact algebraic identity. -/
lemma normalized_identity (k : ℕ) (s : ℂ) :
    modelValue k s/(s-1)^k=
      (((s-1)*riemannZeta s)^k*(DirichletCharacter.LFunction character s)^2)⁻¹ := by
  simp only [modelValue,div_eq_mul_inv,mul_pow,mul_inv_rev,inv_pow]
  ring

/-- An actual nonzero Abel boundary coefficient for the Gaussian sieve
model. This is NOT a Mertens theorem for sharp prime cutoffs. -/
theorem normalized_limit (k : ℕ) :
    Tendsto (fun s : ℂ => modelValue k s/(s-1)^k) (𝓝[≠] 1)
      (𝓝 ((DirichletCharacter.LFunction character 1)^2)⁻¹) := by
  have hL : Tendsto (DirichletCharacter.LFunction character) (𝓝[≠] 1)
      (𝓝 (DirichletCharacter.LFunction character 1)) :=
    continuous_at_one.tendsto.mono_left nhdsWithin_le_nhds
  have hh := (riemannZeta_residue_one.pow k).mul (hL.pow 2)
  have hn := hh.inv₀ (by simpa only [one_pow,one_mul] using pow_ne_zero 2 value_one_nonzero)
  simpa only [normalized_identity,one_pow,one_mul] using hn

theorem normalized_limit_nonzero : ((DirichletCharacter.LFunction character 1)^2)⁻¹≠0 :=
  inv_ne_zero (pow_ne_zero 2 value_one_nonzero)

/-- The at-one prime factor is exactly the complex image of the actual
ordinary/character normalization used in the positive correction product. -/
theorem original_factor (k p : ℕ) [Fact p.Prime] (hp2 : p≠2) :
    (1-(p:ℂ)⁻¹)^k*(1-character p*(p:ℂ)⁻¹)^2=
      (EulerBinomialError318.model k (1/(p:ℝ))
        (quadraticChar (ZMod p) (-1:ZMod p):ℝ):ℂ) := by
  dsimp [EulerBinomialError318.model]
  push_cast
  rw [original_character p hp2]
  simp only [one_div]

/-- Join the constructed positive original-system correction to the actual
Gaussian Euler model. The boundary is Abel/analytic, not a sharp-cutoff
Mertens asymptotic and not a simultaneous prime-pattern theorem. -/
theorem original_corrected_abel {J : Type*} [Fintype J] [DecidableEq J]
    (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C : ℝ, 0<C ∧ HasProd (ActualSieveEulerProduct318.factor κ γ j₀) C ∧
      Tendsto (fun s : ℂ => (C:ℂ)*modelValue (Fintype.card J) s/(s-1)^(Fintype.card J))
        (𝓝[≠] 1) (𝓝 ((C:ℂ)/((DirichletCharacter.LFunction character 1)^2))) ∧
      (C:ℂ)/((DirichletCharacter.LFunction character 1)^2)≠0 := by
  obtain ⟨C,hC,hprod⟩ := ActualSieveEulerProduct318.positive_product κ hκ γ hγ j₀ j₁ h0 h1
  refine ⟨C,hC,hprod,?_,?_⟩
  · have hh := (normalized_limit (Fintype.card J)).const_mul (C:ℂ)
    simpa only [div_eq_mul_inv,mul_assoc] using hh
  · apply div_ne_zero _ (pow_ne_zero 2 value_one_nonzero)
    exact_mod_cast (ne_of_gt hC)

end ActualGaussianEulerModel318
