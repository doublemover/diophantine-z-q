module
public import ActualOriginalQuadraticFourthMoment318
public section
noncomputable section
namespace ActualOriginalShiftedQuadraticMoment318
open MeasureTheory ActualOriginalQuadraticFourthMoment318
open ActualOriginalFiniteFourierEnergy318 ActualOriginalQuadraticEnergyCount318
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma actual_quadratic_continuous (s : Finset ℤ) (c : ℤ) :
    Continuous (fun t : ℝ => quadraticSum s c (t : AddCircle (1 : ℝ))) := by
  unfold quadraticSum frequencySum
  fun_prop

/-- Exact real-interval normalization on EVERY shifted interval of
length one. In particular it applies to the original shifted fundamental
interval, without assuming a periodic-integral rule for the minor subset. -/
lemma actual_shifted_quadratic_moment (s : Finset ℤ) (c : ℤ) (v : ℝ) :
    (∫ t in Set.Ioc v (v+1), ‖quadraticSum s c (t : AddCircle (1 : ℝ))‖^4)=
      ((frequencyEnergy (s.product s) (pairFrequency c)).card : ℝ) := by
  have he := AddCircle.intervalIntegral_preimage (1 : ℝ) v
    (fun θ => ‖quadraticSum s c θ‖^4)
  rw [intervalIntegral.integral_of_le (by linarith),AddCircle.volume_eq_smul_haarAddCircle] at he
  simp only [ENNReal.ofReal_one,one_smul] at he
  exact he.trans (actual_quadratic_fourth_moment s c)

/-- Uniform moments on any actual measurable or nonmeasurable subset
of that interval by nonnegative measure monotonicity. No supremum over
prefixes is moved through an integral. -/
theorem actual_subset_quadratic_moment (H : ℕ) (s : Finset ℤ)
    (hs : s⊆Finset.Icc (-(H : ℤ)) H) (c : ℤ) (hc : c≠0)
    (δ : ℝ) (hδ : 0<δ) (v : ℝ) (D : Set ℝ) (hD : D⊆Set.Ioc v (v+1)) :
    (∫ t in D, ‖quadraticSum s c (t : AddCircle (1 : ℝ))‖^4)≤momentBudget H δ := by
  have hi : IntegrableOn (fun t : ℝ => ‖quadraticSum s c (t : AddCircle (1 : ℝ))‖^4)
      (Set.Ioc v (v+1)) :=
    ((actual_quadratic_continuous s c).norm.pow 4).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hm := setIntegral_mono_set hi (Filter.Eventually.of_forall (fun t => pow_nonneg (norm_nonneg _) 4))
    (Filter.Eventually.of_forall hD)
  rw [actual_shifted_quadratic_moment] at hm
  have hb := actual_bounded_quadratic_fourth_moment H s hs c hc δ hδ
  rw [actual_quadratic_fourth_moment] at hb
  exact hm.trans hb

end ActualOriginalShiftedQuadraticMoment318
