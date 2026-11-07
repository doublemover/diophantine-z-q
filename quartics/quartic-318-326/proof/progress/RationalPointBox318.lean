module
public import RationalAbsoluteHeight
public import PolynomialHeightInterface318
public section
noncomputable section
namespace RationalPointBox318
open ConcreteG8Domain LocalGenerator318 GlobalSaturationHeight318 PolynomialHeightInterface318
open WeierstrassCurve.Affine

lemma pair_zero_ratCast (q : ℚ) : pair q 0 = (q:K) := by
  ext <;> simp [pair]

lemma rational_point_box (q : ℚ) (y : K) (h : E.Nonsingular (pair q 0) y)
    (hx : xHeight (Point.some (pair q 0) y h) < Real.log 9) : PolynomialBox q 0 := by
  simp only [xHeight, Point.xRep_some, Matrix.cons_val_zero, pair_zero_ratCast] at hx
  obtain ⟨hlo,hhi,hdlo,hdhi⟩ := RationalAbsoluteHeight.rational_box_of_absLogHeight_lt K q hx
  exact Or.inl ⟨q.num,q.den,hlo,hhi,hdlo,hdhi,q.num_div_den.symm,rfl⟩

/-- Only the genuinely nonrational number-field height-to-polynomial step
remains as an input here; the rational branch uses the actual absolute height. -/
theorem coverage_of_nonrational
    (nonrat : ∀ u v : ℚ, v ≠ 0 → NumberField.absLogHeight₁ (pair u v) < Real.log 9 →
      PolynomialBox u v) : PolynomialHeightCoverage := by
  intro Q hx
  cases Q with
  | zero => exact Or.inl rfl
  | @some x y h =>
    rcases x with ⟨u,v⟩
    right
    refine ⟨u,v,y,h,rfl,?_⟩
    by_cases hv : v = 0
    · subst v
      exact rational_point_box u y h hx
    · apply nonrat u v hv
      simpa only [xHeight, Point.xRep_some, Matrix.cons_val_zero, pair] using hx

#print axioms pair_zero_ratCast
#print axioms rational_point_box
#print axioms coverage_of_nonrational
end RationalPointBox318
