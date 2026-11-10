module
public import ThreeProjectiveJPoints318
public import ActualThreeProjectivePoints318
public section
noncomputable section
namespace ActualThreeCompactJPoints318
open ProjectiveLineFieldPoints318 ProjectiveLineComplexTopology318
open ActualThreeProjectivePoints318 ActualThreeCuspFilling318 ActualThreeCuspExhaustion318
open ActualThreeExceptionalParameter318 ThreeProjectiveJPoints318 ActualThreeJChartConsumer318
open GammaOneFiber318 PeterssonQuotient318

/-- The exact scheme morphism, transported along the already constructed
compact analytic comparison to genuine projective scheme points. -/
@[expose] def compactJ (z : Filled) : ComplexPoints :=
  mapPoints (compactPointHomeomorph z)

/-- The comparison square commutes at every original quotient point, including
elliptic points: the scheme j morphism equals the original modular j value. -/
theorem original_value (b : Base (image 3)) :
    compactJ (original b) = chartPoint (R:=ℚ) 1 (QuotientJ318.jMap 3 b) := by
  unfold compactJ
  rw [compactPointHomeomorph_original,finite_formula _ (original_finite_denominator_ne_zero b),
    ←original_j_finite]

/-- The original infinite cusp maps to the target reciprocal origin. -/
theorem infinity_value : compactJ (cusp infinityEnd) = chartPoint (R:=ℚ) 0 (0:ℂ) := by
  unfold compactJ
  rw [compactPointHomeomorph_infinity,reciprocal_zero]

/-- The other actual cusp has the same target infinity value. -/
theorem zero_value : compactJ (cusp zeroEnd) = chartPoint (R:=ℚ) 0 (0:ℂ) := by
  unfold compactJ
  rw [compactPointHomeomorph_zero,finite_zero]

/-- Full coverage of the original finite cusp-end type, not only two named
points without an exhaustion theorem. -/
theorem cusp_value (c : FiniteCuspEnds318.End 3) :
    compactJ (cusp c) = chartPoint (R:=ℚ) 0 (0:ℂ) := by
  rcases end_exhaustion c with rfl | rfl
  · exact infinity_value
  · exact zero_value

/-- Any proposed compact modular-j map with the actual original values and
all cusp values is this exact scheme-induced map. No continuity, generic-point
inference or omitted exceptional-point condition is used for this equality. -/
theorem unique_extension (F : Filled → ComplexPoints)
    (hOriginal : ∀ b : Base (image 3),
      F (original b)=chartPoint (R:=ℚ) 1 (QuotientJ318.jMap 3 b))
    (hCusp : ∀ c : FiniteCuspEnds318.End 3,
      F (cusp c)=chartPoint (R:=ℚ) 0 (0:ℂ)) : F=compactJ := by
  funext z
  rcases original_or_cusp z with ⟨b,rfl⟩ | ⟨c,rfl⟩
  · exact (hOriginal b).trans (original_value b).symm
  · exact (hCusp c).trans (cusp_value c).symm

end ActualThreeCompactJPoints318
