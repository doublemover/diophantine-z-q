module
public import ContactOriginalRelativeOverlapCoordinates318
public import RelativeLaurentRingSpan318
public section
noncomputable section
namespace ContactOriginalFiniteRingSpan318
open AlgebraicGeometry CategoryTheory LaurentPolynomial
open ContactOriginalRelativeOverlap318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)

/-- Reflection of the actual old finite projection identifies its literal
ring arrow, rather than assuming an algebraically convenient replacement. -/
lemma old_finite_map : (finiteMap c).toRingHom =
    (Algebra.TensorProduct.includeRight (R := Polynomial ℚ)
      (A := LaurentPolynomial ℚ) (B := ContactKummerOrder318.SourceOrder c)).toRingHom := by
  have h : CommRingCat.ofHom (finiteMap c).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Polynomial ℚ)
        (A := LaurentPolynomial ℚ) (B := ContactKummerOrder318.SourceOrder c)).toRingHom := by
    apply Spec.map_injective
    rw [rationalMap_spec]
    exact ContactOverlapTensorCharts318.finiteIso_inv_chart c
  exact congrArg CommRingCat.Hom.hom h

/-- The actual finite-chart ring spans the ONE old full overlap over the
original Laurent coordinate ring. No open points are discarded. -/
lemma old_span : Submodule.span (LaurentPolynomial ℚ) (Set.range (finiteMap c)) = ⊤ := by
  let P := Submodule.span (LaurentPolynomial ℚ) (Set.range (finiteMap c))
  have hz : ∀ x : oldRing c, x ∈ P := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l b =>
        have hb : (1 : LaurentPolynomial ℚ) ⊗ₜ[Polynomial ℚ] b ∈ P := by
          apply Submodule.subset_span
          refine ⟨b,?_⟩
          exact RingHom.congr_fun (old_finite_map c) b
        have ht : l ⊗ₜ[Polynomial ℚ] b = l • ((1 : LaurentPolynomial ℚ) ⊗ₜ[Polynomial ℚ] b) := by
          rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
        rw [ht]
        exact P.smul_mem l hb
    | add x y hx hy => exact P.add_mem hx hy
  apply top_unique
  intro x _
  exact hz x

variable (R : CommRingCat.{0}) [Algebra ℚ R]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := LaurentPolynomial ℚ) (A := oldRing c)
    (RingHom.ext_rat _ _)

/-- On every actual coefficient test the original finite-chart arrow
spans the same original overlap, over its actual Laurent R action. -/
theorem span : Submodule.span (LaurentPolynomial R)
    (Set.range (RelativeOriginalAffineChartMap318.ringMap (CommRingCat.of ℚ) R
      (ContactOriginalRelativePolynomialCharts318.finiteRing c) (oldRing c) (finiteMap c)).hom) = ⊤ :=
  RelativeLaurentRingSpan318.basechange_span (CommRingCat.of ℚ) R
    (ContactOriginalRelativePolynomialCharts318.finiteRing c) (oldRing c) (finiteMap c) (old_span c)
end ContactOriginalFiniteRingSpan318
