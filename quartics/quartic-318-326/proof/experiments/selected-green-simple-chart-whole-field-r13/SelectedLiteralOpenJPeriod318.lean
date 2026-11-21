module
public import ActualJSurjective318
public import OpenJComplexEvaluation318
public section
noncomputable section
open OpenJModel318 OpenJComplexEvaluation318

namespace SelectedLiteralOpenJPeriod318

theorem ringHom_ext (N : ℕ) (f g : Base N →+* ℂ)
    (hj : f (jCoord N) = g (jCoord N)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · exact hj

/-- Every actual complex point of the literal open j-line is the
SAME ring evaluation from an actual admissible modular period. -/
theorem exists_period_evaluation (N : ℕ) [NeZero N] (f : Base N →+* ℂ) :
    ∃ τ : UpperHalfPlane, ∃ h : Admissible τ, evaluation N τ h = f := by
  obtain ⟨τ,hτ⟩ := ActualJSurjective318.surjective (f (jCoord N))
  have h0 : f (jCoord N) ≠ 0 := isUnit_iff_ne_zero.mp ((base_units N).2.2.2.1.map f)
  have h1' : f (jCoord N-1728) ≠ 0 :=
    isUnit_iff_ne_zero.mp ((base_units N).2.2.2.2.map f)
  have h1 : f (jCoord N) ≠ 1728 := sub_ne_zero.mp (by simpa only [map_sub,map_ofNat] using h1')
  have h : Admissible τ := ⟨hτ.trans_ne h0,hτ.trans_ne h1⟩
  refine ⟨τ,h,ringHom_ext N _ _ ?_⟩
  rw [evaluation_jCoord,hτ]

end SelectedLiteralOpenJPeriod318

#print axioms SelectedLiteralOpenJPeriod318.exists_period_evaluation
