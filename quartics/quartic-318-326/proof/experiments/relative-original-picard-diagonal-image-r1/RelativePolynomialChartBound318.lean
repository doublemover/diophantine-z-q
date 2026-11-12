module
public import RelativePolynomialChartGenerators318
public section
noncomputable section
namespace RelativePolynomialChartBound318
open LaurentPolynomial RelativeLaurentScalar318
set_option maxHeartbeats 650000
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

include hψ in
/-- The negative-chart stability is derived from its ACTUAL reciprocal
polynomial scalar action, not supplied as a new Laurent hypothesis. -/
lemma negative_stable (a : ℤ) (ha : a ≤ 0) (x : M) (hx : x ∈ ψ.range) :
    (T a : LaurentPolynomial R) • x ∈ ψ.range := by
  obtain ⟨y,rfl⟩ := hx
  refine ⟨(Polynomial.X ^ (-a).toNat : Polynomial R) • y,?_⟩
  rw [hψ,Polynomial.toLaurent_X_pow,LaurentPolynomial.invert_T,
    Int.toNat_of_nonneg (show 0 ≤ -a from by omega),neg_neg]

include hφ hψ in
/-- Uniform eventual vanishing for the literal two-chart quotient of
arbitrary original polynomial modules. Finite generation is needed only
on the positive chart; both original localization-spanning statements and
both original scalar actions remain explicit and testable inputs. -/
theorem exists_bound
    (hspanφ : Submodule.span (LaurentPolynomial R) (φ.range : Set M) = ⊤)
    (hspanψ : Submodule.span (LaurentPolynomial R) (ψ.range : Set M) = ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x : M ⧸ RelativeLaurentGeneratorBound318.boundary R M φ.range ψ.range (n : ℤ), x = 0 := by
  obtain ⟨r,g,hgφ,hg⟩ := RelativePolynomialChartGenerators318.exists_generators R M N₀ φ hφ hspanφ
  exact RelativeLaurentGeneratorBound318.exists_quotient_bound R M φ.range ψ.range g hgφ hg
    (RelativePolynomialChartGenerators318.positive_stable R M N₀ φ hφ)
    (negative_stable R M Ninf ψ hψ) hspanψ
end RelativePolynomialChartBound318
