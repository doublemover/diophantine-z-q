module
public import PrimeThreeFirstUResidualCenter318
public import OriginalPrimeThreeFirstUNativeChart318
public section
noncomputable section
namespace PrimeThreeSelectedFirstUResidualCenter318
open PrimeThreeFirstUChartHomExt318 PrimeThreeFirstUResidualPoint318 PrimeThreeFirstUResidualCenter318
open OriginalPrimeThreeFirstOrderPoint318
attribute [local instance] OriginalPrimeThreeFirstURatioChart318.chartAlgebra
attribute [local instance] OriginalPrimeThreeFirstULocalBaseChange318.pointBaseAlgebra
attribute [local instance] OriginalPrimeThreeFirstULocalBaseChange318.chartRightAlgebra

abbrev Base := OriginalPrimeThreeFirstURatioChart318.Base
abbrev LocalU := OriginalPrimeThreeFirstULocalBaseChange318.LocalChart
@[expose] def denominators : Submonoid FirstU :=
  Algebra.algebraMapSubmonoid FirstU OriginalPrimeThreeFirstURatioChart318.rootCenter.primeCompl
@[expose] def chartToLocal : FirstU →+* LocalU := algebraMap FirstU LocalU

local instance actual_chart_localization : IsLocalization denominators LocalU :=
  OriginalPrimeThreeFirstULocalBaseChange318.localChart_center_localization

/-- The selected-point base-change denominators really stay nonzero at
the explicit residual point. This is why that point belongs to the actual
selected first-U chart, not just the coefficient-local presentation. -/
theorem denominator_units (s : denominators) : IsUnit (residualPoint s) := by
  rcases s with ⟨_, ⟨x, hx, rfl⟩⟩
  change IsUnit (residualPoint (OriginalPrimeThreeRetainedChartMaps318.localOrderToChart 0 x))
  rw [RingHom.congr_fun coefficient_factor x]
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply hx
  rw [OriginalPrimeThreeCoefficientRootCenter318.rootCenter_eq_kernel]
  exact RingHom.mem_ker.mpr hz

@[expose] def localResidualPoint : LocalU →+* K :=
  IsLocalization.lift (M := denominators) (S := LocalU) (g := residualPoint) denominator_units
@[simp] theorem localResidualPoint_on_chart (z : FirstU) :
    localResidualPoint (chartToLocal z) = residualPoint z :=
  IsLocalization.lift_eq denominator_units z

theorem localResidualPoint_surjective : Function.Surjective localResidualPoint := by
  intro z
  obtain ⟨x, hx⟩ := residualPoint_surjective z
  exact ⟨chartToLocal x, (localResidualPoint_on_chart x).trans hx⟩

@[expose] def localCenter : Ideal LocalU := center.map chartToLocal

/-- The actual second-center ideal remains the literal three displayed
coordinates after the actual selected-point localization. -/
theorem localCenter_span : localCenter =
    Ideal.span (Set.range (fun j : Fin 3 => chartToLocal (coordinates j))) := by
  rw [localCenter, center, Ideal.map_span, Set.image_range]

/-- Exact kernel, not merely containment of the coordinate ideal. The
reverse inclusion uses native localization fractions and only their proved units. -/
theorem localCenter_eq_kernel : localCenter = RingHom.ker localResidualPoint := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change localResidualPoint (chartToLocal x) = 0
    rw [localResidualPoint_on_chart]
    rw [center_eq_kernel] at hx
    exact RingHom.mem_ker.mp hx
  · intro z hz
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj denominators z
    change z * chartToLocal s = chartToLocal x at hs
    have hx : x ∈ center := by
      rw [center_eq_kernel, RingHom.mem_ker]
      have h := congrArg localResidualPoint hs
      rw [map_mul, localResidualPoint_on_chart, localResidualPoint_on_chart,
        RingHom.mem_ker.mp hz, zero_mul] at h
      exact h.symm
    have hm : chartToLocal x ∈ localCenter := Ideal.mem_map_of_mem chartToLocal hx
    rw [← hs] at hm
    apply (Ideal.unit_mul_mem_iff_mem localCenter (IsLocalization.map_units LocalU s)).mp
    simpa only [mul_comm] using hm

instance localCenter_maximal : localCenter.IsMaximal := by
  rw [localCenter_eq_kernel]
  exact RingHom.ker_isMaximal_of_surjective localResidualPoint localResidualPoint_surjective

/-- Both ratios vanish at the actual residual point. Their inverses are
not available there; in particular a second V/W construction cannot be
forced through the first-U original-root localization. -/
theorem residual_coordinates :
    localResidualPoint (chartToLocal u) = 0 ∧
    localResidualPoint (chartToLocal a) = 0 ∧
    localResidualPoint (chartToLocal b) = 0 := by simp

theorem residual_coordinate_not_unit (j : Fin 3) :
    ¬ IsUnit (chartToLocal (coordinates j)) := by
  intro h
  have h' := h.map localResidualPoint
  fin_cases j <;> simpa [coordinates] using h'

end PrimeThreeSelectedFirstUResidualCenter318
