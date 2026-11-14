module
public import FiniteEulerExclusions318
public section
noncomputable section
namespace EligibleGaussianEulerModel318
open ActualGaussianEulerModel318 ActualGaussianDirichlet318 FiniteEulerExclusions318 Filter
open scoped BigOperators Topology
set_option maxHeartbeats 1000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def eligibleLocal (κ : ℤ) (γ : J → ℤ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  if p∈excluded κ γ then 1 else localModel (Fintype.card J) s p
@[expose] def eligibleValue (κ : ℤ) (γ : J → ℤ) (s : ℂ) : ℂ :=
  modelValue (Fintype.card J) s/omittedProduct κ γ s

/-- Remove EXACTLY the finite set omitted by the original correction
sequence, carrying every missing factor into the explicit denominator. -/
theorem eligible_hasProd (κ : ℤ) (γ : J → ℤ) (s : ℂ) (hs : 1<s.re) :
    HasProd (eligibleLocal κ γ s) (eligibleValue κ γ s) := by
  classical
  have he : (∏ p∈excluded κ γ, eligibleLocal κ γ s p)=1 := by
    apply Finset.prod_eq_one
    intro p hp
    simp only [eligibleLocal,if_pos hp]
  have hh := (model_hasProd (Fintype.card J) s hs).congr_cofinite₀
    (s:=excluded κ γ) (g:=eligibleLocal κ γ s) (fun p hp => model_nonzero _ s hs p)
    (fun p hp => by simp only [eligibleLocal,if_neg hp])
  rw [he] at hh
  simpa only [eligibleValue,omittedProduct,mul_one_div] using hh

/-- The actual excluded-prime product is continuous and nonzero at1,
so finite removal does not destroy the Abel coefficient. -/
theorem eligible_normalized_limit (κ : ℤ) (γ : J → ℤ) :
    Tendsto (fun s : ℂ => eligibleValue κ γ s/(s-1)^(Fintype.card J)) (𝓝[≠] 1)
      (𝓝 (((DirichletCharacter.LFunction character 1)^2)⁻¹/omittedProduct κ γ 1)) := by
  have hD : Tendsto (omittedProduct κ γ) (𝓝[≠] 1) (𝓝 (omittedProduct κ γ 1)) :=
    (omitted_continuous κ γ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh := (normalized_limit (Fintype.card J)).div hD (omitted_one_nonzero κ γ)
  convert hh using 1
  funext s
  dsimp [eligibleValue]
  rw [div_div,div_div,mul_comm (omittedProduct κ γ s)]

/-- The retained at-one factors are exactly those used in the original
positive correction, including the same prime eligibility. -/
theorem eligible_original_factor (κ : ℤ) (γ : J → ℤ) (p : Nat.Primes)
    (h : ActualSieveEulerProduct318.Eligible κ γ (p:ℕ)) :
    letI : Fact (p:ℕ).Prime := ⟨p.2⟩
    eligibleLocal κ γ 1 p=
      (EulerBinomialError318.model (Fintype.card J) (1/(p:ℝ))
        (quadraticChar (ZMod (p:ℕ)) (-1:ZMod (p:ℕ)):ℝ):ℂ) := by
  letI : Fact (p:ℕ).Prime := ⟨p.2⟩
  have hp2 : (p:ℕ)≠2 := by
    have hb := h.2.2
    intro he
    rw [he] at hb
    omega
  rw [eligibleLocal,if_neg ((outside_iff κ γ p).mpr h)]
  simpa only [localModel,Complex.cpow_neg_one] using original_factor (Fintype.card J) (p:ℕ) hp2

/-- Fully aligned Abel coefficient: the actual positive correction and
actual eligible-prime model use the SAME omitted set. The omitted factor D
is constructed and strictly positive, not silently normalized away. -/
theorem original_eligible_abel (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C D : ℝ, 0<C ∧ 0<D ∧
      HasProd (ActualSieveEulerProduct318.factor κ γ j₀) C ∧ omittedProduct κ γ 1=(D:ℂ) ∧
      Tendsto (fun s : ℂ => (C:ℂ)*eligibleValue κ γ s/(s-1)^(Fintype.card J))
        (𝓝[≠] 1) (𝓝 ((C:ℂ)*((DirichletCharacter.LFunction character 1)^2)⁻¹/(D:ℂ))) ∧
      (C:ℂ)*((DirichletCharacter.LFunction character 1)^2)⁻¹/(D:ℂ)≠0 := by
  obtain ⟨C,hC,hprod⟩ := ActualSieveEulerProduct318.positive_product κ hκ γ hγ j₀ j₁ h0 h1
  obtain ⟨D,hD,hDeq⟩ := omitted_one_positive κ γ
  refine ⟨C,D,hC,hD,hprod,hDeq,?_,?_⟩
  · have hh := (eligible_normalized_limit κ γ).const_mul (C:ℂ)
    rw [hDeq] at hh
    simpa only [div_eq_mul_inv,mul_assoc] using hh
  · apply div_ne_zero (mul_ne_zero _ normalized_limit_nonzero)
    · exact_mod_cast (ne_of_gt hC)
    · exact_mod_cast (ne_of_gt hD)

end EligibleGaussianEulerModel318
