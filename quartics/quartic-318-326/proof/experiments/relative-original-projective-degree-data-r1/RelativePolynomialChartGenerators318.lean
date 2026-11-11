module
public import RelativeLaurentGeneratorBound318
public import Mathlib.RingTheory.Finiteness.Defs
public section
noncomputable section
namespace RelativePolynomialChartGenerators318
open LaurentPolynomial RelativeLaurentScalar318
set_option maxHeartbeats 650000
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (N : Type w) [AddCommGroup N] [Module R N] [Module (Polynomial R) N]
  [Module.Finite (Polynomial R) N] (φ : N →ₗ[R] M)
  (hφ : ∀ p : Polynomial R, ∀ x : N, φ (p • x) = (Polynomial.toLaurent p : LaurentPolynomial R) • φ x)

include hφ in
/-- Finite generation of the ORIGINAL polynomial chart supplies a finite
original generating family in its actual overlap image. No free basis or
PID theorem is used, and the Laurent span is derived from the actual map. -/
lemma exists_generators
    (hspan : Submodule.span (LaurentPolynomial R) (φ.range : Set M) = ⊤) :
    ∃ (r : ℕ) (g : Fin r → M), (∀ i, g i ∈ φ.range) ∧
      Submodule.span (LaurentPolynomial R) (Set.range g) = ⊤ := by
  obtain ⟨r,g,hg⟩ := Module.Finite.exists_fin (R := Polynomial R) (M := N)
  refine ⟨r,fun i => φ (g i),fun i => ⟨g i,rfl⟩,?_⟩
  have himage (x : N) : φ x ∈ Submodule.span (LaurentPolynomial R) (Set.range (fun i => φ (g i))) := by
    have hx : x ∈ Submodule.span (Polynomial R) (Set.range g) := by rw [hg]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i,rfl⟩
      exact Submodule.subset_span ⟨i,rfl⟩
    · simpa only [map_zero] using (Submodule.span (LaurentPolynomial R) (Set.range (fun i => φ (g i)))).zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using (Submodule.span (LaurentPolynomial R) (Set.range (fun i => φ (g i)))).add_mem hx hy
    · intro p x _ hx
      rw [hφ]
      exact (Submodule.span (LaurentPolynomial R) (Set.range (fun i => φ (g i)))).smul_mem _ hx
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro y ⟨x,rfl⟩
  exact himage x

include hφ in
lemma positive_stable (a : ℤ) (ha : 0 ≤ a) (x : M) (hx : x ∈ φ.range) :
    (T a : LaurentPolynomial R) • x ∈ φ.range := by
  obtain ⟨y,rfl⟩ := hx
  refine ⟨(Polynomial.X ^ a.toNat : Polynomial R) • y,?_⟩
  rw [hφ,Polynomial.toLaurent_X_pow,Int.toNat_of_nonneg ha]
end RelativePolynomialChartGenerators318
