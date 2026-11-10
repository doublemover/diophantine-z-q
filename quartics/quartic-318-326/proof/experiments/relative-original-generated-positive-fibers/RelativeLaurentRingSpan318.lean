module
public import RelativeLaurentCoefficientTransport318
public import RelativeOriginalAffineChartMap318
public section
noncomputable section
namespace RelativeLaurentRingSpan318
open LaurentPolynomial
open scoped TensorProduct AlgebraMonoidAlgebra
universe u
variable (k R B O : CommRingCat.{u}) [Algebra k R] [Algebra k B] [Algebra k O]
  [Algebra (LaurentPolynomial k) O] [IsScalarTower k (LaurentPolynomial k) O]
  (g : B →ₐ[k] O)

/-- Generation by an ORIGINAL chart ring survives arbitrary coefficient
base change, for the original tensor arrow and the actual Laurent scalar
pushout. No reducedness, flatness, field, finite basis or localization
comparison is supplied on the new coefficient ring. -/
theorem basechange_span
    (hO : Submodule.span (LaurentPolynomial k) (Set.range g) = ⊤) :
    Submodule.span (LaurentPolynomial R)
      (Set.range (RelativeOriginalAffineChartMap318.ringMap k R B O g).hom) = ⊤ := by
  let P := Submodule.span (LaurentPolynomial R)
    (Set.range (RelativeOriginalAffineChartMap318.ringMap k R B O g).hom)
  have hsingle (r : R) (o : O) : r ⊗ₜ[k] o ∈ P := by
    have ho : o ∈ Submodule.span (LaurentPolynomial k) (Set.range g) := by rw [hO]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ho
    · rintro _ ⟨b,rfl⟩
      exact Submodule.subset_span ⟨r ⊗ₜ[k] b,by
        simp only [RelativeOriginalAffineChartMap318.ringMap,CommRingCat.hom_ofHom,
          AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Algebra.TensorProduct.map_tmul,AlgHom.id_apply]⟩
    · simpa only [TensorProduct.tmul_zero] using P.zero_mem
    · intro x y _ _ hx hy
      simpa only [TensorProduct.tmul_add] using P.add_mem hx hy
    · intro l x _ hx
      have ht : r ⊗ₜ[k] (l • x) =
          (algebraMap (LaurentPolynomial k) (LaurentPolynomial R) l) • (r ⊗ₜ[k] x) := by
        change r ⊗ₜ[k] (algebraMap (LaurentPolynomial k) O l * x) =
          RelativeOriginalLaurentAlgebra318.laurentMap k R O
            (algebraMap (LaurentPolynomial k) (LaurentPolynomial R) l) * (r ⊗ₜ[k] x)
        rw [RelativeLaurentCoefficientTransport318.original_scalar,
          Algebra.TensorProduct.tmul_mul_tmul,one_mul]
      rw [ht]
      exact P.smul_mem _ hx
  apply top_unique
  intro z _
  induction z using TensorProduct.inductionOn with
  | tmul r o => exact hsingle r o
  | add x y hx hy => exact P.add_mem hx hy
end RelativeLaurentRingSpan318
