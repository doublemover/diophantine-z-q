module
public import SieveEulerCorrection318
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public section
noncomputable section
namespace ActualSieveEulerProduct318
open FixedSieveExceptionalPrimes318 SieveEulerCorrection318
set_option maxHeartbeats 1000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Precisely the good large primes; all other indices contribute identity. -/
@[expose] def Eligible (κ : ℤ) (γ : J → ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ p∉exceptionalPrimes κ γ ∧ 16*(Fintype.card J+2)≤p

@[expose] def factor (κ : ℤ) (γ : J → ℤ) (j₀ : J) (p : ℕ) : ℝ := by
  classical
  exact if h : Eligible κ γ p then
    letI : Fact p.Prime := ⟨h.1⟩
    correction (Fintype.card J) (1/(p:ℝ)) (quadraticChar (ZMod p) (-1:ZMod p):ℝ)
      (FiniteSieveDensity318.density (κ : ZMod p) (fun j => (γ j : ZMod p)) j₀ : ℝ)
  else 1

/-- The existing literal finite-density estimate supplies the real analytic
input. It is constructed from the coefficient system, never assumed. -/
lemma actual_real_error (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (p : ℕ) [Fact p.Prime]
    (hout : p∉exceptionalPrimes κ γ) :
    |(FiniteSieveDensity318.density (κ : ZMod p) (fun j => (γ j : ZMod p)) j₀ : ℝ)-
      ((Fintype.card J:ℝ)+2*(quadraticChar (ZMod p) (-1:ZMod p):ℝ))*(1/(p:ℝ))|≤
      4*((Fintype.card J:ℝ)+1)*(1/(p:ℝ))^2 := by
  have hh := outside_density_error κ hκ γ hγ j₀ j₁ h0 h1 p hout
  have hr : |(FiniteSieveDensity318.density (κ : ZMod p) (fun j => (γ j : ZMod p)) j₀ : ℝ)-
      ((Fintype.card J:ℝ)+2*(quadraticChar (ZMod p) (-1:ZMod p):ℝ))/(p:ℝ)|≤
      4*((Fintype.card J:ℝ)+1)/(p:ℝ)^2 := by exact_mod_cast hh
  simpa only [div_pow,one_pow,mul_one_div] using hr

lemma small_inverse (p k : ℕ) (hp : p.Prime) (hlarge : 16*(k+2)≤p) :
    0≤1/(p:ℝ) ∧ ((k:ℝ)+2)*(1/(p:ℝ))≤1/16 := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hb : 16*((k:ℝ)+2)≤p := by exact_mod_cast hlarge
  refine ⟨le_of_lt (one_div_pos.mpr hp0),?_⟩
  rw [mul_one_div]
  apply (div_le_iff₀ hp0).mpr
  linarith

/-- Every factor of this concrete original-system product is positive. -/
theorem factor_positive (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (p : ℕ) :
    0<factor κ γ j₀ p := by
  classical
  unfold factor
  split_ifs with h
  · letI : Fact p.Prime := ⟨h.1⟩
    obtain ⟨hx,hsmall⟩ := small_inverse p (Fintype.card J) h.1 h.2.2
    have he : (quadraticChar (ZMod p) (-1:ZMod p):ℝ)=1 ∨
        (quadraticChar (ZMod p) (-1:ZMod p):ℝ)= -1 := by
      exact_mod_cast (quadraticChar_dichotomy (show (-1:ZMod p)≠0 from neg_ne_zero.mpr one_ne_zero))
    exact correction_positive _ _ _ _ hx hsmall he
      (actual_real_error κ hκ γ hγ j₀ j₁ h0 h1 p h.2.1)
  · norm_num

/-- A uniform p^-2 bound over all natural indices, with excluded indices
contributing zero error. No distribution theorem for primes is needed. -/
theorem factor_error (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (p : ℕ) :
    |factor κ γ j₀ p-1|≤errorConstant (Fintype.card J)/(p:ℝ)^2 := by
  classical
  unfold factor
  split_ifs with h
  · letI : Fact p.Prime := ⟨h.1⟩
    obtain ⟨hx,hsmall⟩ := small_inverse p (Fintype.card J) h.1 h.2.2
    have hkx0 : 0≤(Fintype.card J:ℝ)*(1/(p:ℝ)) := mul_nonneg (Nat.cast_nonneg _) hx
    have he : (quadraticChar (ZMod p) (-1:ZMod p):ℝ)=1 ∨
        (quadraticChar (ZMod p) (-1:ZMod p):ℝ)= -1 := by
      exact_mod_cast (quadraticChar_dichotomy (show (-1:ZMod p)≠0 from neg_ne_zero.mpr one_ne_zero))
    have hh := correction_error (Fintype.card J) (1/(p:ℝ)) _ _ hx (by nlinarith)
      (by nlinarith) he (actual_real_error κ hκ γ hγ j₀ j₁ h0 h1 p h.2.1)
    simpa only [div_pow,one_pow,mul_one_div] using hh
  · simp only [sub_self,abs_zero]
    dsimp [errorConstant]
    positivity

/-- At each retained prime the correction splits the ACTUAL survivor density,
not a separately postulated asymptotic or surrogate local polynomial. -/
theorem factor_decomposition (κ : ℤ) (γ : J → ℤ) (j₀ : J) (p : ℕ)
    (h : Eligible κ γ p) :
    letI : Fact p.Prime := ⟨h.1⟩
    1-(FiniteSieveDensity318.density (κ : ZMod p) (fun j => (γ j : ZMod p)) j₀ : ℝ)=
      factor κ γ j₀ p*EulerBinomialError318.model (Fintype.card J) (1/(p:ℝ))
        (quadraticChar (ZMod p) (-1:ZMod p):ℝ) := by
  classical
  letI : Fact p.Prime := ⟨h.1⟩
  obtain ⟨hx,hsmall⟩ := small_inverse p (Fintype.card J) h.1 h.2.2
  have hkx0 : 0≤(Fintype.card J:ℝ)*(1/(p:ℝ)) := mul_nonneg (Nat.cast_nonneg _) hx
  have he : (quadraticChar (ZMod p) (-1:ZMod p):ℝ)=1 ∨
      (quadraticChar (ZMod p) (-1:ZMod p):ℝ)= -1 := by
    exact_mod_cast (quadraticChar_dichotomy (show (-1:ZMod p)≠0 from neg_ne_zero.mpr one_ne_zero))
  have hm := EulerBinomialError318.model_lower (Fintype.card J) (1/(p:ℝ)) _ hx
    (by nlinarith) (by nlinarith) he
  have hmn : EulerBinomialError318.model (Fintype.card J) (1/(p:ℝ))
      (quadraticChar (ZMod p) (-1:ZMod p):ℝ)≠0 := by linarith
  simp only [factor,dif_pos h,correction,div_mul_cancel₀ _ hmn]

/-- Absolute convergence is deduced from the actual computed local factors. -/
theorem error_summable (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    Summable (fun p : ℕ => |factor κ γ j₀ p-1|) := by
  have hs : Summable (fun p : ℕ => 1/(p:ℝ)^2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have hc := hs.mul_left (errorConstant (Fintype.card J))
  apply hc.of_nonneg_of_le (fun p => abs_nonneg _)
  intro p
  simpa only [mul_one_div] using factor_error κ hκ γ hγ j₀ j₁ h0 h1 p

/-- The original-system Euler correction converges to a strictly positive
real value. This is NOT the unnormalized survivor product or a prime-pattern
asymptotic: the ordinary and character first-order factors were removed. -/
theorem positive_product (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C : ℝ, 0<C ∧ HasProd (factor κ γ j₀) C := by
  have habs := error_summable κ hκ γ hγ j₀ j₁ h0 h1
  have hn : Summable (fun p : ℕ => ‖factor κ γ j₀ p-1‖) := by
    simpa only [Real.norm_eq_abs] using habs
  have hs := Real.summable_log_one_add_of_summable hn.of_norm
  have hlog : Summable (fun p : ℕ => Real.log (factor κ γ j₀ p)) := by
    have he (x : ℝ) : 1+(x-1)=x := by ring
    simpa only [he] using hs
  refine ⟨Real.exp (∑' p : ℕ, Real.log (factor κ γ j₀ p)),Real.exp_pos _,?_⟩
  exact Real.hasProd_of_hasSum_log (factor_positive κ hκ γ hγ j₀ j₁ h0 h1) hlog.hasSum

end ActualSieveEulerProduct318
