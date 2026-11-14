module
public import ActualOriginalUniformTranslateSupport318
public section
noncomputable section
namespace ActualOriginalContinuousPeriodization318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalUniformTranslateSupport318 ContinuousMap
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def translate (f : C(Coordinates ℝ,ℂ)) (z : Coordinates ℤ) : C(Coordinates ℝ,ℂ) :=
  ⟨fun x => f (integerEmbed z+x),f.continuous.comp (continuous_const.add continuous_id)⟩

lemma actual_translates_locally_summable_norm (f : C(Coordinates ℝ,ℂ))
    (hf : HasCompactSupport f) (K : TopologicalSpace.Compacts (Coordinates ℝ)) :
    Summable (fun z : Coordinates ℤ => ‖(translate f z).restrict K‖) := by
  classical
  obtain ⟨s,hs⟩ := actual_uniform_translate_support f hf K.isCompact
  apply summable_of_hasFiniteSupport
  apply s.finite_toSet.subset
  intro z hz
  by_contra hnot
  apply hz
  apply norm_eq_zero.mpr
  ext x
  exact hs x x.property z hnot

lemma actual_translates_summable (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f) :
    Summable (translate f) :=
  summable_of_locally_summable_norm (actual_translates_locally_summable_norm f hf)

/-- The continuous periodization exists in the compact-open continuous
function space because of PRODUCED local uniform finite support. -/
@[expose] def periodization (f : C(Coordinates ℝ,ℂ)) : C(Coordinates ℝ,ℂ) :=
  ∑' z : Coordinates ℤ, translate f z

lemma actual_periodization_apply (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (x : Coordinates ℝ) :
    periodization f x = ∑' z : Coordinates ℤ, f (integerEmbed z+x) := by
  exact (ContinuousMap.tsum_apply (actual_translates_summable f hf) x).symm

/-- Genuine periodicity under EVERY original integer translation. -/
theorem actual_periodization_periodic (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (z : Coordinates ℤ) (x : Coordinates ℝ) :
    periodization f (integerEmbed z+x) = periodization f x := by
  rw [actual_periodization_apply f hf,actual_periodization_apply f hf]
  simpa only [Equiv.addRight_apply,integerEmbed_add,add_assoc] using
    (Equiv.addRight z).tsum_eq (fun n : Coordinates ℤ => f (integerEmbed n+x))

/-- On each actual compact set, the produced periodization agrees with
one FINITE sum uniformly on that entire set. -/
theorem actual_periodization_finite_on_compact (f : C(Coordinates ℝ,ℂ))
    (hf : HasCompactSupport f) {K : Set (Coordinates ℝ)} (hK : IsCompact K) :
    ∃ s : Finset (Coordinates ℤ), ∀ x ∈ K,
      periodization f x = ∑ z ∈ s, f (integerEmbed z+x) := by
  classical
  obtain ⟨s,hs⟩ := actual_uniform_translate_support f hf hK
  refine ⟨s,fun x hx => ?_⟩
  rw [actual_periodization_apply f hf]
  exact tsum_eq_sum (fun z hz => hs x hx z hz)

end ActualOriginalContinuousPeriodization318
