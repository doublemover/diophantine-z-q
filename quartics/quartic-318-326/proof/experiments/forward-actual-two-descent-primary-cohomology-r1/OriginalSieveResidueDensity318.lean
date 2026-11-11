module
public import FiniteSieveDensity318
public section
noncomputable section
namespace OriginalSieveResidueDensity318
open FiniteSieveDensity318
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact excluded coefficient-difference primes imply injectivity on
the original residue coefficients, with no index silently discarded. -/
theorem residue_injective (p : ℕ) (γ : ι → ℤ)
    (havoid : ∀ i j, i≠j → ¬(p:ℤ)∣γ j-γ i) :
    Function.Injective (fun i => (γ i:ZMod p)) := by
  intro i j he
  by_contra hij
  exact havoid i j hij ((ZMod.intCast_eq_intCast_iff_dvd_sub (γ i) (γ j) p).mp he)

/-- Apply the complete finite count to the original integer coefficient
system at every prime outside precisely the named exceptional divisors. -/
theorem original_density (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (κ : ℤ) (hκ : ¬(p:ℤ)∣κ) (γ : ι → ℤ)
    (havoid : ∀ i j, i≠j → ¬(p:ℤ)∣γ j-γ i)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ) :
    density (κ:ZMod p) (fun i => (γ i:ZMod p)) i₀=
      (((p:ℚ)-1)*(nonzeroCount (F:=ZMod p):ℚ)*
        (2*(nuZero (F:=ZMod p):ℚ)+((Fintype.card ι:ℚ)-2)*(nonzeroCount (F:=ZMod p):ℚ))+
        (nuZero (F:=ZMod p):ℚ)^2-1)/((p:ℚ)^4-1) := by
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ:ZMod p)≠0 := by
    intro he
    exact hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  have hc0 : (γ i₀:ZMod p)=0 := by rw [h0,Int.cast_zero]
  have hc1 : (γ i₁:ZMod p)= -(κ:ZMod p) := by rw [h1,Int.cast_neg]
  simpa only [ZMod.card] using density_formula hF (GoodReductionResidue318.two_residue_ne p hp2)
    (κ:ZMod p) hk (fun i => (γ i:ZMod p)) (residue_injective p γ havoid) i₀ i₁ hc0 hc1

end OriginalSieveResidueDensity318
