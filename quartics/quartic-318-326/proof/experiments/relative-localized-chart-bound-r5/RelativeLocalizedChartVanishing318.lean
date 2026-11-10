module
public import RelativeLocalizedChartMap318
public section
noncomputable section
namespace RelativeLocalizedChartVanishing318
open CategoryTheory LaurentPolynomial RelativeLaurentScalar318
universe u
variable (R : Type u) [CommRing R]
  (N₀ N∞ : ModuleCat.{u} (Polynomial R))
  [Module.Finite (Polynomial R) N₀]
  (M : ModuleCat.{u} (LaurentPolynomial R))
  (e₀ : (ModuleCat.extendScalars (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)).obj N₀ ≅ M)
  (e∞ : (ModuleCat.extendScalars (RelativeLocalizedChartBound318.reciprocal R)).obj N∞ ≅ M)
local instance : Module R N₀ := Module.compHom N₀ Polynomial.C
local instance : Module R N∞ := Module.compHom N∞ Polynomial.C
local instance : Module R M := coefficientModule R M

/-- The original positive-chart comparison, with its actual coefficient action. -/
def positive : N₀ →ₗ[R] M :=
  RelativeLocalizedChartMap318.map R Polynomial.toLaurent N₀ M e₀
    (fun r => Polynomial.toLaurent_C r)

/-- The original reciprocal-chart comparison, with its actual coefficient action. -/
def negative : N∞ →ₗ[R] M :=
  RelativeLocalizedChartMap318.map R (RelativeLocalizedChartBound318.reciprocal R) N∞ M e∞
    (fun r => by
      change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C r)) = C r
      rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C])

/-- An arbitrary-ring finite-chart bound with NO separately assumed scalar
laws, image stability, finite overlap basis or localization-spanning input.
The two actual extension isomorphisms determine all these data through
original adjunction units. The quotient still is the literal two-chart
coefficient quotient, not an assigned derived-cohomology carrier. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : M ⧸ RelativeLaurentGeneratorBound318.boundary R M
      (positive R N₀ M e₀).range (negative R N∞ M e∞).range (n : ℤ), x = 0 := by
  apply RelativeLocalizedChartBound318.exists_bound R M N₀ N∞
    (positive R N₀ M e₀) (negative R N∞ M e∞)
    (fun p x => RelativeLocalizedChartMap318.map_polynomial R Polynomial.toLaurent N₀ M e₀ _ p x)
    (fun p x => RelativeLocalizedChartMap318.map_polynomial R
      (RelativeLocalizedChartBound318.reciprocal R) N∞ M e∞ _ p x)
    e₀ e∞
  · intro x
    rfl
  · intro x
    rfl
end RelativeLocalizedChartVanishing318
