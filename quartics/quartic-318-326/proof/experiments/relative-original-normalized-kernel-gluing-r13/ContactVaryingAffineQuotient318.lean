module
public import CyclicQuotientFiniteFlat318
public import ContactOriginalRelativePolynomialCharts318
public section
noncomputable section
namespace ContactVaryingAffineQuotient318
open AlgebraicGeometry CategoryTheory CyclicQuotientEvaluation318
open ContactOriginalRelativePolynomialCharts318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

/-- The rings of the SAME two original affine contact charts after the
specified coefficient extension. No fixed line or section is introduced. -/
abbrev finiteAlgebra := R ⊗[ℚ] finiteRing c
abbrev infinityAlgebra := R ⊗[ℚ] infinityRing c

variable {M : Type} [AddCommGroup M] [Module R M]
  {ι : Type} [Fintype ι] (b : Module.Basis ι R M) (v : M)
include b

/-- Actual varying quotients on the original finite contact chart. The
cyclic action is data to be represented by matrix/vector charts next. -/
theorem finite_chart
    (ρ : finiteAlgebra R c →ₐ[R] Module.End R M)
    (h : Function.Surjective (evaluation ρ v)) :
    IsClosedImmersion (CyclicQuotientFiniteFlat318.into ρ v) ∧
      IsFinite (CyclicQuotientFiniteFlat318.projection ρ v) ∧
      Flat (CyclicQuotientFiniteFlat318.projection ρ v) :=
  ⟨inferInstance,CyclicQuotientFiniteFlat318.finite ρ v b h,
    CyclicQuotientFiniteFlat318.flat ρ v b h⟩

/-- The reciprocal chart keeps its actual original integral-closure ring.
Agreement across their real overlap and global gluing remain separate. -/
theorem infinity_chart
    (ρ : infinityAlgebra R c →ₐ[R] Module.End R M)
    (h : Function.Surjective (evaluation ρ v)) :
    IsClosedImmersion (CyclicQuotientFiniteFlat318.into ρ v) ∧
      IsFinite (CyclicQuotientFiniteFlat318.projection ρ v) ∧
      Flat (CyclicQuotientFiniteFlat318.projection ρ v) :=
  ⟨inferInstance,CyclicQuotientFiniteFlat318.finite ρ v b h,
    CyclicQuotientFiniteFlat318.flat ρ v b h⟩
end ContactVaryingAffineQuotient318
