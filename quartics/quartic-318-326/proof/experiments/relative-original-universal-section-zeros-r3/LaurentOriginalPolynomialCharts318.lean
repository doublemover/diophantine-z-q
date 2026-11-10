module
public import LaurentCechSectionsFinite318

public section
noncomputable section
namespace LaurentOriginalPolynomialCharts318
open LaurentVectorFiltration318 LaurentTransitionBounds318
open scoped BigOperators
open Polynomial LaurentPolynomial
universe u
variable {k : Type u} [Field k] {n : ℕ}

/-- Componentwise original polynomial-to-Laurent localization. -/
def finiteMap : (Fin n → Polynomial k) →ₗ[k] V k n where
  toFun p i := Polynomial.toLaurent (p i)
  map_add' p q := by funext i; simp
  map_smul' c p := by
    funext i
    exact (Polynomial.toLaurentAlg (R:=k)).map_smul c (p i)

lemma finiteMap_single (i : Fin n) (a : ℕ) :
    finiteMap (Pi.single i (Polynomial.X ^ a)) = monomial (k:=k) i a := by
  ext j
  by_cases h : j=i
  · subst j
    simp [finiteMap,monomial,Pi.single_apply]
  · simp [finiteMap,monomial,Pi.single_apply,h,Ne.symm h]

lemma polynomial_single_positive (i : Fin n) (p : Polynomial k) :
    Pi.single i (Polynomial.toLaurent p) ∈ positive (k:=k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have he : (Pi.single i (Polynomial.toLaurent (p+q)) : V k n) =
          (Pi.single i (Polynomial.toLaurent p) : V k n) + (Pi.single i (Polynomial.toLaurent q) : V k n) := by
        ext j
        by_cases h : j=i <;> simp_all [Pi.single_apply]
      rw [he]
      exact positive.add_mem hp hq
  | monomial a c =>
      have he : Pi.single i (Polynomial.toLaurent (Polynomial.monomial a c)) =
          c • monomial (k:=k) i a := by
        ext j
        by_cases h : j=i
        · subst j
          simp [monomial,Pi.single_apply,LaurentPolynomial.smul_eq_C_mul]
        · simp [monomial,Pi.single_apply,h,Ne.symm h]
      rw [he]
      exact positive.smul_mem c (monomial_mem i a (Int.natCast_nonneg a))

/-- The positive filtration is exactly the image of the original finite
polynomial chart, not just an auxiliary span with a similar dimension. -/
theorem finiteMap_range : LinearMap.range (finiteMap (k:=k) (n:=n)) = positive := by
  apply le_antisymm
  · rintro v ⟨p,rfl⟩
    have he : finiteMap p = ∑ i : Fin n, Pi.single i (Polynomial.toLaurent (p i)) := by
      ext j
      simp [finiteMap,Pi.single_apply]
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => polynomial_single_positive i (p i))
  · apply Submodule.span_le.mpr
    rintro v ⟨i,a,ha,rfl⟩
    refine ⟨Pi.single i (Polynomial.X ^ a.toNat),?_⟩
    rw [finiteMap_single,Int.toNat_of_nonneg ha]

/-- Original inversion T↦T⁻¹, component by component. -/
def inversion : V k n →ₗ[k] V k n where
  toFun v i := LaurentPolynomial.invert (v i)
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

lemma inversion_monomial (i : Fin n) (a : ℤ) :
    inversion (monomial (k:=k) i a) = monomial i (-a) := by
  ext j
  by_cases h : j=i <;> simp_all [inversion,monomial,Pi.single_apply]

lemma inversion_positive {v : V k n} (hv : v ∈ positive) :
    inversion v ∈ negative := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro w ⟨i,a,ha,rfl⟩
    rw [inversion_monomial]
    exact monomial_mem i (-a) (by change -a ≤ 0; omega)
  · simpa using (negative (k:=k) (n:=n)).zero_mem
  · intro x y _ _ hx hy
    simpa only [map_add] using negative.add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using negative.smul_mem c hx

/-- The original infinity polynomial chart uses the original inversion. -/
def infinityMap : (Fin n → Polynomial k) →ₗ[k] V k n := inversion.comp finiteMap

/-- The negative filtration is exactly the image of the original infinity
polynomial chart. -/
theorem infinityMap_range : LinearMap.range (infinityMap (k:=k) (n:=n)) = negative := by
  apply le_antisymm
  · rintro v ⟨p,rfl⟩
    apply inversion_positive
    rw [← finiteMap_range]
    exact ⟨p,rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨i,a,ha,rfl⟩
    refine ⟨Pi.single i (Polynomial.X ^ (-a).toNat),?_⟩
    change inversion (finiteMap _) = _
    rw [finiteMap_single,inversion_monomial]
    have h : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    rw [h,neg_neg]

/-- The boundary retained by the finite-dimensional theorem is exactly the
sum of the two original polynomial chart images under the original transition. -/
theorem original_boundary (e : V k n ≃ₗ[LaurentPolynomial k] V k n) :
    LaurentCechFinite318.boundary e = LinearMap.range finiteMap ⊔
      (LinearMap.range infinityMap).map (underlying e) := by
  rw [finiteMap_range,infinityMap_range] <;> rfl
end LaurentOriginalPolynomialCharts318
