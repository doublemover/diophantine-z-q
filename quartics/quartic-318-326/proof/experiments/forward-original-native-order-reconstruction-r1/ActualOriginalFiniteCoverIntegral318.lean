module
public import ActualOriginalRationalCellIntegral318
public section
noncomputable section
namespace ActualOriginalFiniteCoverIntegral318
open MeasureTheory
open scoped BigOperators

/-- Finite OVERLAPPING covers are used by domination with their indicator
sum. Disjointness is not presumed, and the complete cover multiplicity
remains on the right. -/
theorem actual_finite_cover_integral {ι : Type*} (I : Finset ι)
    (s : Set ℝ) (hs : MeasurableSet s) (T : ι → Set ℝ)
    (hT : ∀ i∈I, MeasurableSet (T i)) (hTs : ∀ i∈I, T i⊆s)
    (hcover : s⊆⋃ i∈I, T i) (f : ℝ → ℂ) (hf : IntegrableOn f s) :
    ‖∫ t in s, f t‖≤∑ i∈I, ∫ t in T i, ‖f t‖ := by
  classical
  have hi (i : ι) (h : i∈I) :
      Integrable (fun t => (T i).indicator (fun x => ‖f x‖) t) (volume.restrict s) :=
    hf.norm.indicator (hT i h)
  have hh : ∀ t∈s, ‖f t‖≤∑ i∈I, (T i).indicator (fun x => ‖f x‖) t := by
    intro t ht
    obtain ⟨i,hi',hti⟩ := Set.mem_iUnion₂.mp (hcover ht)
    calc
      ‖f t‖=(T i).indicator (fun x => ‖f x‖) t := (Set.indicator_of_mem hti _).symm
      _≤∑ j∈I, (T j).indicator (fun x => ‖f x‖) t :=
        Finset.single_le_sum (fun j _ => by
          by_cases hj : t∈T j
          · rw [Set.indicator_of_mem hj]; exact norm_nonneg _
          · simp only [Set.indicator_of_notMem hj,le_refl]) hi'
  apply (norm_integral_le_integral_norm _).trans
  have hb := setIntegral_mono_on hf.norm (integrable_finsetSum I hi) hs hh
  rw [integral_finsetSum I hi] at hb
  apply hb.trans_eq
  apply Finset.sum_congr rfl
  intro i hi'
  rw [setIntegral_indicator (hT i hi'),Set.inter_eq_right.mpr (hTs i hi')]

end ActualOriginalFiniteCoverIntegral318
