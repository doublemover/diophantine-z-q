module
public import ProjectiveCoefficientRestriction318
public import ContactRelativeChartFinitePresentation318
public section
noncomputable section
namespace RelativePolynomialChartProjective318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R B : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ B]
  [Algebra (Polynomial ℚ) B] [IsScalarTower ℚ (Polynomial ℚ) B]
  [Module.Free (Polynomial ℚ) B] [Module.Finite (Polynomial ℚ) B]
  (L : Line (Spec (CommRingCat.of (R ⊗[ℚ] B))))

/-- Actual finite polynomial chart algebra stays finite free after
coefficient extension, via the canonical original polynomial pushout. -/
theorem algebra_free : Module.Free (Polynomial R) (R ⊗[ℚ] B) := by
  letI : Module.Free (Polynomial R) (Polynomial R ⊗[Polynomial ℚ] B) :=
    Module.Free.of_basis ((Module.Free.chooseBasis (Polynomial ℚ) B).baseChange (Polynomial R))
  exact Module.Free.of_equiv (RelativeOriginalPolynomialAlgebra318.polynomialComparison ℚ R B).toLinearEquiv

/-- The original arbitrary line has a finite polynomial retract, not
an assumed globally free chart basis over arbitrary coefficient R. -/
theorem sections_projective : Module.Projective (Polynomial R)
    (RelativeOriginalChartSections318.sections (CommRingCat.of ℚ) R B L) := by
  letI := algebra_free R B
  letI := (OriginalLineAffineModel318.properties (CommRingCat.of (R ⊗[ℚ] B)) L).1
  exact ProjectiveCoefficientRestriction318.projective (Polynomial R) (R ⊗[ℚ] B) _

theorem sections_retract : ∃ (r : ℕ)
    (out : RelativeOriginalChartSections318.sections (CommRingCat.of ℚ) R B L →ₗ[Polynomial R]
      Fin r → Polynomial R)
    (back : (Fin r → Polynomial R) →ₗ[Polynomial R]
      RelativeOriginalChartSections318.sections (CommRingCat.of ℚ) R B L),
    back.comp out = LinearMap.id := by
  letI := sections_projective R B L
  obtain ⟨r,back,out,_,_,h⟩ := Module.Finite.exists_comp_eq_id_of_projective
    (Polynomial R) (RelativeOriginalChartSections318.sections (CommRingCat.of ℚ) R B L)
  exact ⟨r,out,back,h⟩
end RelativePolynomialChartProjective318
