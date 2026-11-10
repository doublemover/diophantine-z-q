module
public import RelativePolynomialChartBound318
public import ScalarExtensionOriginalSpan318
public section
noncomputable section
namespace RelativeLocalizedChartBound318
open CategoryTheory LaurentPolynomial RelativeLaurentScalar318
universe u
variable (R : Type u) [CommRing R]
  (M : Type u) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (N₀ Ninf : Type u)
  [AddCommGroup N₀] [Module R N₀] [Module (Polynomial R) N₀]
  [Module.Finite (Polynomial R) N₀]
  [AddCommGroup Ninf] [Module R Ninf] [Module (Polynomial R) Ninf]
  (φ : N₀ →ₗ[R] M) (ψ : Ninf →ₗ[R] M)
  (hφ : ∀ p : Polynomial R, ∀ x : N₀,
    φ (p • x) = (Polynomial.toLaurent p : LaurentPolynomial R) • φ x)
  (hψ : ∀ p : Polynomial R, ∀ x : Ninf,
    ψ (p • x) = (LaurentPolynomial.invert (Polynomial.toLaurent p) : LaurentPolynomial R) • ψ x)

/-- The actual reciprocal polynomial-to-Laurent map, retaining its direction. -/
def reciprocal : Polynomial R →+* LaurentPolynomial R :=
  (LaurentPolynomial.invert (R := R)).toRingHom.comp
    Polynomial.toLaurent

include hφ hψ in
/-- The original two chart restriction maps have an eventual vanishing
quotient as soon as their original scalar-extension comparisons and unit
formulas are known. Neither localization-spanning nor monomial stability
is an input; both are derived on the original displayed modules. -/
theorem exists_bound
    (e₀ : (ModuleCat.extendScalars (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)).obj
      (ModuleCat.of (Polynomial R) N₀) ≅ ModuleCat.of (LaurentPolynomial R) M)
    (einf : (ModuleCat.extendScalars (reciprocal R)).obj
      (ModuleCat.of (Polynomial R) Ninf) ≅ ModuleCat.of (LaurentPolynomial R) M)
    (he₀ : ∀ x : N₀, e₀.hom ((ModuleCat.extendRestrictScalarsAdj Polynomial.toLaurent).unit.app
      (ModuleCat.of (Polynomial R) N₀) x) = φ x)
    (heinf : ∀ x : Ninf, einf.hom ((ModuleCat.extendRestrictScalarsAdj (reciprocal R)).unit.app
      (ModuleCat.of (Polynomial R) Ninf) x) = ψ x) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x : M ⧸ RelativeLaurentGeneratorBound318.boundary R M φ.range ψ.range (n : ℤ), x = 0 := by
  have h₀ := ScalarExtensionOriginalSpan318.original_span
    (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)
    (ModuleCat.of (Polynomial R) N₀) (ModuleCat.of (LaurentPolynomial R) M) e₀ φ he₀
  have hinf := ScalarExtensionOriginalSpan318.original_span (reciprocal R)
    (ModuleCat.of (Polynomial R) Ninf) (ModuleCat.of (LaurentPolynomial R) M) einf ψ heinf
  exact RelativePolynomialChartBound318.exists_bound R M N₀ Ninf φ ψ hφ hψ h₀ hinf
end RelativeLocalizedChartBound318
