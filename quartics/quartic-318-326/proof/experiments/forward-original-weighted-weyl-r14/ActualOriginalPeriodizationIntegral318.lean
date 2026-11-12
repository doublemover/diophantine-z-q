module
public import ActualOriginalContinuousPeriodization318
public section
noncomputable section
namespace ActualOriginalPeriodizationIntegral318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalUniformTranslateSupport318 ActualOriginalContinuousPeriodization318
open MeasureTheory Set
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def closedCube : Set (Coordinates ℝ) :=
  (Icc (0 : ℝ) 1 ×ˢ Icc 0 1) ×ˢ (Icc 0 1 ×ˢ Icc 0 1) ×ˢ Icc 0 1

lemma actual_closed_cube_compact : IsCompact closedCube :=
  (isCompact_Icc.prod isCompact_Icc).prod ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)

lemma actual_cube_subset_closed : originalCube ⊆ closedCube := by
  rintro x ⟨⟨ha,hb⟩,⟨⟨hc,hd⟩,hw⟩⟩
  exact ⟨⟨⟨ha.1,ha.2.le⟩,⟨hb.1,hb.2.le⟩⟩,
    ⟨⟨⟨hc.1,hc.2.le⟩,⟨hd.1,hd.2.le⟩⟩,⟨hw.1,hw.2.le⟩⟩⟩

/-- The genuine sum/integral exchange is proved from one FINITE active
translate set uniform on the closed cube. It is not assumed from pointwise
summability. The countable tiling then recovers the original integral. -/
theorem actual_original_periodization_integral (f : C(Coordinates ℝ,ℂ))
    (hf : HasCompactSupport f) :
    (∫ x in originalCube, periodization f x) = ∫ x : Coordinates ℝ, f x := by
  classical
  have hi : Integrable (f : Coordinates ℝ → ℂ) :=
    f.continuous.integrable_of_hasCompactSupport hf
  have hiz (z : Coordinates ℤ) : Integrable (fun x : Coordinates ℝ => f (integerEmbed z+x)) :=
    hi.comp_measurePreserving (measurePreserving_add_left volume (integerEmbed z))
  obtain ⟨s,hs⟩ := actual_uniform_translate_support f hf actual_closed_cube_compact
  have he (x : Coordinates ℝ) (hx : x ∈ originalCube) :
      periodization f x = ∑ z ∈ s, f (integerEmbed z+x) := by
    rw [actual_periodization_apply f hf]
    exact tsum_eq_sum (fun z hz => hs x (actual_cube_subset_closed hx) z hz)
  have hz (z : Coordinates ℤ) (hnot : z ∉ s) :
      (∫ x in originalCube, f (integerEmbed z+x)) = 0 := by
    calc
      _ = ∫ x in originalCube, (0 : ℂ) :=
        setIntegral_congr_fun originalCube_measurable
          (fun x hx => hs x (actual_cube_subset_closed hx) z hnot)
      _ = 0 := by simp
  calc
    (∫ x in originalCube, periodization f x) =
        ∫ x in originalCube, ∑ z ∈ s, f (integerEmbed z+x) :=
      setIntegral_congr_fun originalCube_measurable he
    _ = ∑ z ∈ s, ∫ x in originalCube, f (integerEmbed z+x) :=
      integral_finsetSum s (fun z _ => (hiz z).integrableOn)
    _ = ∑' z : Coordinates ℤ, ∫ x in originalCube, f (integerEmbed z+x) :=
      (tsum_eq_sum hz).symm
    _ = ∫ x : Coordinates ℝ, f x := (actual_original_integral_tiling f hi).symm

end ActualOriginalPeriodizationIntegral318
