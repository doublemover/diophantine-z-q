module
public import LaurentCechFinite318

public section
noncomputable section
namespace LaurentCechSectionsFinite318
open LaurentVectorFiltration318 LaurentTransitionBounds318
universe u
variable {k : Type u} [Field k] {n : ℕ}

/-- Actual matching vectors for the two charts, recorded in the first chart's
coordinates on the unchanged overlap. -/
abbrev H0 (e : V k n ≃ₗ[LaurentPolynomial k] V k n) :=
  ↥(positive (k:=k) (n:=n) ⊓ negative.map (underlying e))

lemma section_upper (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (b : ℤ) (hb : ∀ i : Fin n, e (monomial i 0) ∈ upper b) (v : H0 e) :
    v.val ∈ upper b := by
  obtain ⟨w,hw,he⟩ := v.property.2
  change e w = v.val at he
  rw [← he]
  simpa only [zero_add] using map_upper e b hb 0 hw

lemma section_coeff_zero (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (b : ℤ) (hb : ∀ i : Fin n, e (monomial i 0) ∈ upper b)
    (v : H0 e) (i : Fin n) (a : ℤ) (ha : a ∉ Set.Icc 0 b) :
    (v.val i).coeff a = 0 := by
  by_cases h : 0 ≤ a
  · exact coeff_eq_zero (section_upper e b hb v) i a (by
      intro hab
      exact ha ⟨h,hab⟩)
  · exact coeff_eq_zero v.property.1 i a h

/-- Restrict the original Laurent coefficients to a finite interval. -/
def coefficients (e : V k n ≃ₗ[LaurentPolynomial k] V k n) (b : ℤ) :
    H0 e →ₗ[k] (Fin n → Set.Icc (0 : ℤ) b → k) where
  toFun v i a := (v.val i).coeff a.val
  map_add' v w := by funext i a; simp
  map_smul' c v := by funext i a; simp

lemma coefficients_injective (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (b : ℤ) (hb : ∀ i : Fin n, e (monomial i 0) ∈ upper b) :
    Function.Injective (coefficients e b) := by
  intro v w h
  apply Subtype.ext
  funext i
  apply LaurentPolynomial.ext
  intro a
  by_cases ha : a ∈ Set.Icc 0 b
  · exact congrFun (congrFun h i) ⟨a,ha⟩
  · rw [section_coeff_zero e b hb v i a ha,section_coeff_zero e b hb w i a ha]

/-- The actual matching-vector space is finite-dimensional. The bound comes
from the actual transition, not a premise about global sections. -/
theorem finite_h0 (e : V k n ≃ₗ[LaurentPolynomial k] V k n) :
    FiniteDimensional k (H0 e) := by
  obtain ⟨b,hb⟩ := exists_column_bound e
  letI : Fintype (Set.Icc (0 : ℤ) b) := (Set.finite_Icc 0 b).fintype
  exact Module.Finite.of_injective (coefficients e b) (coefficients_injective e b hb)
end LaurentCechSectionsFinite318
