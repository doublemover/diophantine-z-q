module
public import ActualOriginalScaledNonzeroModeBound318
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public section
noncomputable section
namespace ActualOriginalNonzeroModeSum318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalIntegerLattice318
open ActualOriginalScaledNonzeroModeBound318
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- A finite, actual rank-five original-lattice constant. Zero contributes
zero to the inverse sixth power, rather than an omitted infinite term. -/
@[expose] def latticeSixthMass : ℝ :=
  ∑' m : Coordinates ℤ, (‖integerEmbed m‖⁻¹)^6

lemma latticeSixthMass_nonneg : 0 ≤ latticeSixthMass :=
  tsum_nonneg (fun _ => by positivity)

/-- Exactly the nonzero part of the original Poisson series, retaining
all integer dual vectors and removing only its literal zero vector. -/
@[expose] def nonzeroDualTerm (κ : ℕ) (q : ℕ) [NeZero q] (a : ℤ)
    (R t : ℝ) (W : Coordinates ℝ → ℝ) (m : Coordinates ℤ) : ℂ :=
  if m=0 then 0 else scaledDualTerm κ q a R t W m

/-- The same global parameter constants control the WHOLE nonzero
series. Absolute summability is produced by the original rank-five lattice
p-series before the quantitative infinite-sum inequality is used. -/
theorem actual_nonzero_series_bound (κ : ℕ) (hκ : 0 < κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], ∀ a : ℤ,
      IsUnit (a : ZMod q) → ∀ (R t : ℝ), 0 < R →
      Summable (fun m : Coordinates ℤ => ‖nonzeroDualTerm κ q a R t W m‖) ∧
      ‖∑' m : Coordinates ℤ, nonzeroDualTerm κ q a R t W m‖ ≤
        (Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5)*C*(1+‖t‖)^k/R)*latticeSixthMass := by
  obtain ⟨k,C,hC,hbound⟩ := actual_nonzero_mode_bound κ hκ W hW hWc
  refine ⟨k,C,hC,fun q _ a ha R t hR => ?_⟩
  let A : ℝ := Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5)*C*(1+‖t‖)^k/R
  have hterm (m : Coordinates ℤ) :
      ‖nonzeroDualTerm κ q a R t W m‖ ≤ A*(‖integerEmbed m‖⁻¹)^6 := by
    by_cases hm : m=0
    · simp only [nonzeroDualTerm,hm,ite_true,norm_zero,integerEmbed_zero,
        inv_zero,zero_pow (by omega : (6:ℕ) ≠ 0),mul_zero,le_refl]
    · simpa only [nonzeroDualTerm,hm,ite_false,A] using hbound q a ha R t hR m hm
  have hmajor := actual_integer_norm_inverse_six.mul_left A
  have hnorm : Summable (fun m : Coordinates ℤ => ‖nonzeroDualTerm κ q a R t W m‖) :=
    hmajor.of_norm_bounded (fun m => by simpa only [norm_norm] using hterm m)
  refine ⟨hnorm,?_⟩
  have hb := tsum_of_norm_bounded hmajor.hasSum hterm
  simpa only [tsum_mul_left,latticeSixthMass,A] using hb

end ActualOriginalNonzeroModeSum318
