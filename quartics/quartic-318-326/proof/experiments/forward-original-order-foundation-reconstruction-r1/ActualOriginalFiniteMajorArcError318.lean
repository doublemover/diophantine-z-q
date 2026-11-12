module
public import ActualOriginalIntegratedArcError318
public section
noncomputable section
namespace ActualOriginalFiniteMajorArcError318
open QuadricCRTAssembly318 ActualOriginalNonzeroModeSum318 ActualOriginalIntegratedArcError318
open scoped ContDiff BigOperators
set_option maxHeartbeats 16000000

/-- Sum over EXACTLY denominators1 through N and their unit numerators,
using each canonical residue representative. Modulus1 is retained. This is
an indexed arc sum; disjointness of arcs is a separate geometric question. -/
@[expose] def finiteMajorArcError (κ N : ℕ) (B T : ℝ) (W : Coordinates ℝ → ℝ) : ℂ :=
  ∑ q : Fin N, ∑ a : {a : ZMod (q.val+1) // IsUnit a},
    integratedArcError κ (q.val+1) (a.val.val : ℤ) B T W

/-- Literal finite arithmetic factor, retaining actual unit counts and
all even/bad-prime denominators. -/
@[expose] def finiteArcMass (κ N : ℕ) : ℝ :=
  ∑ q : Fin N, ∑ _a : {a : ZMod (q.val+1) // IsUnit a},
    Real.sqrt (32*(κ : ℝ)*((q.val+1 : ℕ) : ℝ)^5)*((q.val+1 : ℕ) : ℝ)

lemma finiteArcMass_nonneg (κ N : ℕ) : 0 ≤ finiteArcMass κ N := by
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro a ha
  positivity

/-- Accumulation over every actual unit numerator and every retained
denominator preserves an explicit B^-3 error. Constants k,C do not depend
on the denominator cutoff or beta-window cutoff. -/
theorem actual_finite_major_arc_error (κ : ℕ) (hκ : 0 < κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (N : ℕ) (B T : ℝ), 0 < B → 0 ≤ T →
      ‖finiteMajorArcError κ N B T W‖ ≤
        (C*(1+T)^k*(2*T)*latticeSixthMass*finiteArcMass κ N)/B^3 := by
  obtain ⟨k,C,hC,hbound⟩ := actual_integrated_arc_error κ hκ W hW hWc
  refine ⟨k,C,hC,fun N B T hB hT => ?_⟩
  have hn : ‖finiteMajorArcError κ N B T W‖ ≤
      ∑ q : Fin N, ∑ a : {a : ZMod (q.val+1) // IsUnit a},
        (2*T*Real.sqrt (32*(κ : ℝ)*((q.val+1 : ℕ) : ℝ)^5)*C*(1+T)^k*
          ((q.val+1 : ℕ) : ℝ)*latticeSixthMass)/B^3 := by
    unfold finiteMajorArcError
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro q hq
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro a ha
    apply hbound (q.val+1) (a.val.val : ℤ) _ B T hB hT
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using a.property
  convert hn using 1
  simp only [finiteArcMass,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  ring

end ActualOriginalFiniteMajorArcError318
