module
public import ContactOriginalRelativeLineOverlap318
public import ContactOriginalInfinityRingSpan318
public import ScalarRestrictionOriginalSpan318
public import RelativePolynomialChartBound318
public section
noncomputable section
namespace ContactOriginalRelativeOverlapSpan318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativeOverlap318 ContactOriginalRelativePolynomialCharts318
open ContactOriginalRelativeLineOverlap318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
/-- Compatibility of the native LEFT tensor actions, without replacing
those actions by a separately inferred Algebra.toSMul structure. -/
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) where
  smul_assoc q l z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        simp only [TensorProduct.smul_tmul']
        rw [smul_assoc]
    | add x y hx hy =>
        simp only [smul_add,hx,hy]

/-- The unchanged whole-overlap section carrier with the original Laurent
coordinate action, not coordinates on a separately chosen free module. -/
local instance laurentModule : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L)
    (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance laurentTower : IsScalarTower (LaurentPolynomial R) (ring R c)
    (originalSections R c L) := IsScalarTower.of_compHom ..

/-- Both actual whole-chart restrictions span the SAME unchanged original
line-section module. The actual ring spans are produced, not hypotheses. -/
theorem finite_span : Submodule.span (LaurentPolynomial R)
    (Set.range (finiteRestriction R c L)) = ⊤ := by
  exact ScalarRestrictionOriginalSpan318.original_span (C := LaurentPolynomial R)
    (finiteArrow R c).hom _ (originalSections R c L)
    (OriginalAffineLinePathSections318.comparison (finiteArrow R c)
      (finiteLine R c L) (line R c L) (finiteComparison R c L))
    (finiteRestriction R c L) (finite_unit R c L)
    (ContactOriginalFiniteRingSpan318.span c R)

theorem infinity_span : Submodule.span (LaurentPolynomial R)
    (Set.range (infinityRestriction R c L)) = ⊤ := by
  exact ScalarRestrictionOriginalSpan318.original_span (C := LaurentPolynomial R)
    (infinityArrow R c).hom _ (originalSections R c L)
    (OriginalAffineLinePathSections318.comparison (infinityArrow R c)
      (infinityLine R c L) (line R c L) (infinityComparison R c L))
    (infinityRestriction R c L) (infinity_unit R c L)
    (ContactOriginalInfinityRingSpan318.span c R)

local instance : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R (originalSections R c L)
local instance : Module R (finiteSections R c L) :=
  Module.compHom (finiteSections R c L) Polynomial.C
local instance : Module R (infinitySections R c L) :=
  Module.compHom (infinitySections R c L) Polynomial.C

/-- The actual geometric finite restriction, now with its PROVED original
coefficient linearity, for use in the original coefficient quotient. -/
@[expose] def finiteMap : finiteSections R c L →ₗ[R] originalSections R c L where
  toFun := finiteRestriction R c L
  map_add' := OriginalAffineLinePathSections318.restriction_add _ _ _ _
  map_smul' r m := by
    change finiteRestriction R c L ((Polynomial.C r : Polynomial R) • m) =
      ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (C r) • finiteRestriction R c L m
    simpa only [Polynomial.toLaurent_C] using finite_polynomial R c L (Polynomial.C r) m

/-- The second map retains the genuine reciprocal coordinate action. -/
@[expose] def infinityMap : infinitySections R c L →ₗ[R] originalSections R c L where
  toFun := infinityRestriction R c L
  map_add' := OriginalAffineLinePathSections318.restriction_add _ _ _ _
  map_smul' r m := by
    change infinityRestriction R c L ((Polynomial.C r : Polynomial R) • m) =
      ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (C r) • infinityRestriction R c L m
    simpa only [Polynomial.toLaurent_C,LaurentPolynomial.invert_C] using
      infinity_polynomial R c L (Polynomial.C r) m

/-- For every original line on every actual affine coefficient test,
ONE bound kills all sufficiently positive literal shifted overlap
quotients. No caller-supplied spanning, finite basis, denominator bound,
nonreduced acyclicity or chart compatibility is left in this theorem.
The separate identification with geometrically twisted derived H1 is NOT
asserted here; this endpoint is the exact original coefficient quotient. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : originalSections R c L ⧸ RelativeLaurentGeneratorBound318.boundary R
      (originalSections R c L) (finiteMap R c L).range (infinityMap R c L).range (n : ℤ), x = 0 := by
  apply RelativePolynomialChartBound318.exists_bound R (originalSections R c L)
    (finiteSections R c L) (infinitySections R c L) (finiteMap R c L) (infinityMap R c L)
  · exact finite_polynomial R c L
  · exact infinity_polynomial R c L
  · exact finite_span R c L
  · exact infinity_span R c L
end ContactOriginalRelativeOverlapSpan318
