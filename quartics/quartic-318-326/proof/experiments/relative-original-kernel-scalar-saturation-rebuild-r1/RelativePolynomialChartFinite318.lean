module
public import RelativeLaurentFiniteQuotient318
public section
noncomputable section
namespace RelativePolynomialChartFinite318
open LaurentPolynomial RelativeLaurentScalar318
universe u v w z
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (N₀ : Type w) [AddCommGroup N₀] [Module R N₀] [Module (Polynomial R) N₀]
  [Module.Finite (Polynomial R) N₀]
  (Ninf : Type z) [AddCommGroup Ninf] [Module R Ninf] [Module (Polynomial R) Ninf]
  (φ : N₀ →ₗ[R] M) (ψ : Ninf →ₗ[R] M)
  (hφ : ∀ p : Polynomial R, ∀ x : N₀, φ (p • x) = (Polynomial.toLaurent p : LaurentPolynomial R) • φ x)
  (hψ : ∀ p : Polynomial R, ∀ x : Ninf, ψ (p • x) =
    (LaurentPolynomial.invert (Polynomial.toLaurent p) : LaurentPolynomial R) • ψ x)

include hφ hψ in
/-- The literal, unshifted original coefficient quotient is finite. The
only finite input is the actual positive polynomial module; the finite
exponent window is produced from its original generators and the actual
negative-chart denominator bounds. -/
theorem finite_quotient
    (hspanφ : Submodule.span (LaurentPolynomial R) (φ.range : Set M) = ⊤)
    (hspanψ : Submodule.span (LaurentPolynomial R) (ψ.range : Set M) = ⊤) :
    Module.Finite R (M ⧸ (φ.range ⊔ ψ.range)) := by
  obtain ⟨r,g,hgφ,hg⟩ := RelativePolynomialChartGenerators318.exists_generators R M N₀ φ hφ hspanφ
  exact RelativeLaurentFiniteQuotient318.finite_quotient R M φ.range ψ.range g hgφ hg
    (RelativePolynomialChartGenerators318.positive_stable R M N₀ φ hφ)
    (RelativePolynomialChartBound318.negative_stable R M Ninf ψ hψ) hspanψ
end RelativePolynomialChartFinite318
