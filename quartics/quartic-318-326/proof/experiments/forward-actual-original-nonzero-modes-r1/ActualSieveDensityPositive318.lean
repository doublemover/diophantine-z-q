module
public import ActualSlicePolynomialPreparation318
public section
noncomputable section
namespace ActualSieveDensityPositive318
open FiniteSieveDensity318 FiniteFiveQuadricCount318
set_option maxHeartbeats 2000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Strict positivity of the actual original local density, including the
two-form inert case where the first-order term vanishes. -/
theorem density_positive (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (κ : F) (hκ : κ≠0) (γ : J → F) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    0<density κ γ j₀ := by
  have hj : j₀≠j₁ := by
    intro hh
    have he : (0:F)= -κ := by rw [←h0,hh,h1]
    exact hκ (neg_eq_zero.mp he.symm)
  letI : Nontrivial J := ⟨⟨j₀,j₁,hj⟩⟩
  have hk : (2:ℤ)≤Fintype.card J := by
    have hh : (1:ℤ)<Fintype.card J := by exact_mod_cast (Fintype.one_lt_card (α:=J))
    omega
  have hq : (2:ℤ)≤Fintype.card F := by
    have hh : (1:ℤ)<Fintype.card F := by exact_mod_cast (Fintype.one_lt_card (α:=F))
    omega
  have he := quadraticChar_dichotomy (show (-1:F)≠0 from neg_ne_zero.mpr one_ne_zero)
  have hn : 1≤nonzeroCount (F:=F) ∧ 1≤nuZero (F:=F) := by
    rcases he with he|he
    · dsimp [nonzeroCount,nuZero]
      rw [he]
      constructor <;> nlinarith
    · dsimp [nonzeroCount,nuZero]
      rw [he]
      constructor <;> nlinarith
  have hA : 0<((Fintype.card F:ℤ)-1)*nonzeroCount (F:=F) :=
    mul_pos (by omega) (by omega)
  have hN : 0<((Fintype.card F:ℤ)-1)*nonzeroCount (F:=F)*
        (2*nuZero (F:=F)+((Fintype.card J:ℤ)-2)*nonzeroCount (F:=F))+
        (nuZero (F:=F))^2-1 := by
    have hp : 0≤((Fintype.card J:ℤ)-2)*nonzeroCount (F:=F) :=
      mul_nonneg (by omega) (by omega)
    have hB : 0<2*nuZero (F:=F)+((Fintype.card J:ℤ)-2)*nonzeroCount (F:=F) := by omega
    have hAB := mul_pos hA hB
    nlinarith [sq_nonneg (nuZero (F:=F)-1)]
  have hnum : 0<(Nat.card {z : Total κ γ // z≠totalOrigin κ γ j₀}:ℚ) := by
    have hh := primitive_card hF h2 κ hκ γ hγ j₀ j₁ h0 h1
    have hi : (0:ℤ)<Nat.card {z : Total κ γ // z≠totalOrigin κ γ j₀} := by
      rw [hh]
      exact hN
    exact_mod_cast hi
  have hden : 0<(Nat.card {z : Quadric κ // z≠origin κ}:ℚ) := by
    rw [nonzero_quadric_card hF h2 κ hκ]
    have hq' : 1<Fintype.card F := Fintype.one_lt_card
    have hq2 : (1:ℤ)<(Fintype.card F:ℤ)^2 := by nlinarith
    have hq4i : (1:ℤ)<(Fintype.card F:ℤ)^4 := by nlinarith [sq_nonneg ((Fintype.card F:ℤ)^2-1)]
    have hq4 : 1<(Fintype.card F)^4 := by exact_mod_cast hq4i
    have hh : 0<Fintype.card F^4-1 := by omega
    exact_mod_cast hh
  exact div_pos hnum hden

/-- Eligible original primes satisfy the complete strict local-density
hypotheses needed by the actual Selberg sieve, not just an asymptotic. -/
theorem eligible_density_bounds (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (p : ℕ)
    (hel : ActualSieveEulerProduct318.Eligible κ γ p) :
    letI : Fact p.Prime := ⟨hel.1⟩
    0<(density (κ:ZMod p) (fun j => (γ j:ZMod p)) j₀:ℝ) ∧
      (density (κ:ZMod p) (fun j => (γ j:ZMod p)) j₀:ℝ)<1 := by
  letI : Fact p.Prime := ⟨hel.1⟩
  obtain ⟨hp2,hkp,havoid⟩ := FixedSieveExceptionalPrimes318.outside_conditions
    κ hκ γ hγ p hel.1 hel.2.1
  have hf : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ:ZMod p)≠0 := by
    intro hh
    exact hkp ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp hh)
  have hc0 : (γ j₀:ZMod p)=0 := by rw [h0,Int.cast_zero]
  have hc1 : (γ j₁:ZMod p)= -(κ:ZMod p) := by rw [h1,Int.cast_neg]
  constructor
  · exact_mod_cast density_positive hf (GoodReductionResidue318.two_residue_ne p hp2)
      (κ:ZMod p) hk (fun j => (γ j:ZMod p))
      (OriginalSieveResidueDensity318.residue_injective p γ havoid) j₀ j₁ hc0 hc1
  · obtain ⟨hx,hsmall⟩ := ActualSieveEulerProduct318.small_inverse p (Fintype.card J) hel.1 hel.2.2
    have he : (quadraticChar (ZMod p) (-1:ZMod p):ℝ)=1 ∨
        (quadraticChar (ZMod p) (-1:ZMod p):ℝ)= -1 := by
      exact_mod_cast quadraticChar_dichotomy (show (-1:ZMod p)≠0 from neg_ne_zero.mpr one_ne_zero)
    have hk0 : (0:ℝ)≤Fintype.card J := Nat.cast_nonneg _
    have hkx0 := mul_nonneg hk0 hx
    have hm := EulerBinomialError318.model_lower (Fintype.card J) (1/(p:ℝ)) _ hx
      (by nlinarith)
      (by nlinarith) he
    have hmp : 0<EulerBinomialError318.model (Fintype.card J) (1/(p:ℝ))
        (quadraticChar (ZMod p) (-1:ZMod p):ℝ) := by linarith
    have hfp := ActualSieveEulerProduct318.factor_positive κ hκ γ hγ j₀ j₁ h0 h1 p
    have hid := ActualSieveEulerProduct318.factor_decomposition κ γ j₀ p hel
    have hh := mul_pos hfp hmp
    rw [←hid] at hh
    linarith

end ActualSieveDensityPositive318
