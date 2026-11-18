module
public import ActualOriginalMinorRationalCells318
public section
noncomputable section
namespace ActualOriginalRationalCellIntegral318
open QuadricCRTAssembly318 ActualOriginalScaledCircle318
open ActualOriginalFullFiveLogarithmicBound318 ActualOriginalReciprocalLogBudget318
open ActualOriginalMinorRationalCells318 MeasureTheory
open scoped ContDiff

@[expose] def rationalWeylEnvelope (κ : ℤ) (R C B : ℝ) (q : ℤ) : ℝ :=
  Real.sqrt (C*(2*R+4)^5*
    (((16*(⌈R*B⌉ : ℝ)/(q : ℝ)+2)*logBlockBudget (2*(⌈R*B⌉ : ℝ)+1) q)^4*
    ((16*((|κ|*⌈R*B⌉ : ℤ) : ℝ)/(q : ℝ)+2)*logBlockBudget (2*(⌈R*B⌉ : ℝ)+1) q)))

/-- The produced five-variable bound, not a postulated cell amplitude.
The same R,C works for every scale, cell and rational approximation. -/
theorem actual_rational_cell_bounds (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R C : ℝ, 1≤R ∧ 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ N Q : ℕ,
      ∀ a q : ℤ, 0<q → q≤Q → IsCoprime q a →
      (∀ t∈minorCell N Q B a q, ‖scaledCircleSum κ t B W‖≤rationalWeylEnvelope κ R C B q) ∧
      (∫ t in minorCell N Q B a q, ‖scaledCircleSum κ t B W‖)≤
        rationalWeylEnvelope κ R C B q*(2*dirichletWidth Q q) := by
  obtain ⟨R,C,hR,hC,hbound⟩ := actual_smooth_full_five_logarithmic_bound κ hκ W hW hc
  refine ⟨R,C,hR,hC,fun B hB N Q a q hq hqQ hcop => ?_⟩
  have hqr : (0 : ℝ)<q := by exact_mod_cast hq
  have hqR : (q : ℝ)≤Q := by exact_mod_cast hqQ
  have hp (t : ℝ) (ht : t∈minorCell N Q B a q) :
      ‖scaledCircleSum κ t B W‖≤rationalWeylEnvelope κ R C B q := by
    have he : |t-(a : ℝ)/(q : ℝ)|≤1/(((Q : ℝ)+1)*(q : ℝ)) := by
      apply abs_le.mpr
      have hh := ht.2
      dsimp [dirichletWidth] at hh
      constructor <;> linarith [hh.1,hh.2]
    have he' : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2 := by
      apply he.trans
      apply one_div_le_one_div_of_le (sq_pos_of_pos hqr)
      nlinarith
    have hh := hbound B hB a q hq hcop t he'
    have hepos := (sq_nonneg ‖scaledCircleSum κ t B W‖).trans hh
    have hsqrt := Real.sq_sqrt hepos
    have hspos := Real.sqrt_nonneg (C*(2*R+4)^5*
      (((16*(⌈R*B⌉ : ℝ)/(q : ℝ)+2)*logBlockBudget (2*(⌈R*B⌉ : ℝ)+1) q)^4*
      ((16*((|κ|*⌈R*B⌉ : ℤ) : ℝ)/(q : ℝ)+2)*logBlockBudget (2*(⌈R*B⌉ : ℝ)+1) q)))
    dsimp [rationalWeylEnvelope]
    nlinarith [norm_nonneg (scaledCircleSum κ t B W)]
  refine ⟨hp,?_⟩
  have hfin : volume (minorCell N Q B a q)<⊤ := by
    apply lt_of_le_of_lt (measure_mono Set.inter_subset_right)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hb := norm_setIntegral_le_of_norm_le_const (f:=fun t => ‖scaledCircleSum κ t B W‖)
    hfin (fun t ht => by simpa only [norm_norm] using hp t ht)
  have hnon : 0≤∫ t in minorCell N Q B a q, ‖scaledCircleSum κ t B W‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnon] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (actual_minor_cell_measure N Q B a q hq)
    (Real.sqrt_nonneg _))

end ActualOriginalRationalCellIntegral318
