module
public import ActualSelectedEulerLower318
public section
noncomputable section
namespace ActualOriginalEulerLogGrowth318
open ActualSelectedEulerLower318 ActualOriginalEulerComparison318 ActualRemovedEulerFactor318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The ORIGINAL full Euler denominator has its genuine logarithmic
power growth. Every positive constant is produced from the actual
character L-value, finite excluded factors and original correction.
There is no supplied Mertens bound or boundary Euler convergence. -/
theorem actual_full_euler_log_growth (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C : ℝ,0<C ∧ ∀ N,2≤N →
      C*(Real.log (N:ℝ))^(Fintype.card J)≤fullEuler κ γ j₀ N := by
  obtain ⟨U,hU,hordinary⟩ := actual_selected_ordinary_lower κ γ
  obtain ⟨c,hc,hcharacter⟩ := actual_selected_character_lower κ γ
  obtain ⟨V,hV,hcompare⟩ := actual_uniform_euler_comparison κ hκ γ hγ j₀ j₁ h0 h1
  refine ⟨c^2/(V*U^(Fintype.card J)),by positivity,?_⟩
  intro N hN
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hbase : 0≤Real.log (N:ℝ)/U := div_nonneg hlog hU.le
  have hpow := pow_le_pow_left₀ hbase (hordinary N (by omega)) (Fintype.card J)
  have hsquare := pow_le_pow_left₀ hc.le (hcharacter N) 2
  have hmul := mul_le_mul hpow hsquare (sq_nonneg c)
    (pow_nonneg (ordinary_euler_pos κ γ N).le _)
  have hdiv := div_le_div_of_nonneg_right hmul hV.le
  have he : c^2/(V*U^(Fintype.card J))*(Real.log (N:ℝ))^(Fintype.card J)=
      (Real.log (N:ℝ)/U)^(Fintype.card J)*c^2/V := by
    rw [div_pow]
    field_simp [hU.ne',hV.ne'] <;> ring
  rw [he]
  exact hdiv.trans (hcompare N)

end ActualOriginalEulerLogGrowth318
