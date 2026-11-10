module
public import ContactRelativeOriginalHZero318
public import ContactRelativeFiniteLaurentPushout318
public import ContactRelativeInfinityLaurentPushout318
public import OriginalPolynomialCoordinateLocalization318
public import ReciprocalImageUniformBound318
public import RelativePolynomialChartProjective318
public section
noncomputable section
namespace ContactRelativeGlobalCoordinateBounds318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 FiniteLaurentVectorFiltration318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module (LaurentPolynomial R) (originalSections R c L) := overlapLaurentModule R c L
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤

@[expose] def finiteCoordinates {r : ℕ}
    (out : finiteSections R c L →ₗ[Polynomial R] Fin r → Polynomial R) :
    originalSections R c L →ₗ[LaurentPolynomial R] Fin r → LaurentPolynomial R :=
  OriginalPolynomialCoordinateLocalization318.map R Polynomial.toLaurent _ _
    (ContactRelativeFiniteLaurentPushout318.sections R c L) out

lemma finite_coordinates_unit {r : ℕ}
    (out : finiteSections R c L →ₗ[Polynomial R] Fin r → Polynomial R) (x : finiteSections R c L) :
    finiteCoordinates R c L out (finiteRestriction R c L x) = fun i => Polynomial.toLaurent (out x i) := by
  rw [← ContactRelativeFiniteLaurentPushout318.sections_unit]
  exact OriginalPolynomialCoordinateLocalization318.unit R Polynomial.toLaurent _ _ _ out x

/-- ONE actual finite-coordinate degree bound for ALL original global
sections, produced from actual infinity generators and original restriction
compatibility. It is not a bound supplied by the caller. -/
theorem finite_bound {r : ℕ}
    (out : finiteSections R c L →ₗ[Polynomial R] Fin r → Polynomial R) :
    ∃ b : ℕ, ∀ s : Γ(L.object,⊤),
      (fun i => Polynomial.toLaurent (out (ContactRelativeOriginalHZero318.pair R c L s).1 i)) ∈
        (upper (b : ℤ) : Submodule R (V R (Fin r))) := by
  obtain ⟨b,hb⟩ := ReciprocalImageUniformBound318.exists_bound R (infinitySections R c L)
    (originalSections R c L) (ContactOriginalRelativeOverlapSpan318.infinityMap R c L).toAddMonoidHom
    (infinity_polynomial R c L) (finiteCoordinates R c L out)
  refine ⟨b,fun s => ?_⟩
  have h := sub_eq_zero.mp (ContactRelativeOriginalHZero318.compatible R c L s)
  change finiteRestriction R c L (ContactRelativeOriginalHZero318.pair R c L s).1 =
    infinityRestriction R c L (ContactRelativeOriginalHZero318.pair R c L s).2 at h
  rw [← finite_coordinates_unit,h]
  exact hb _

@[expose] def invertVector (r : ℕ) : V R (Fin r) →+ V R (Fin r) where
  toFun v i := invert (v i)
  map_zero' := by ext i; exact map_zero _
  map_add' x y := by ext i; exact map_add _ _ _

lemma invert_smul (r : ℕ) (a : LaurentPolynomial R) (v : V R (Fin r)) :
    invertVector R r (a • v) = invert a • invertVector R r v := by
  ext i
  exact map_mul _ a (v i)

@[expose] def infinityCoordinates {r : ℕ}
    (out : infinitySections R c L →ₗ[Polynomial R] Fin r → Polynomial R) :
    originalSections R c L →ₗ[LaurentPolynomial R] Fin r → LaurentPolynomial R :=
  OriginalPolynomialCoordinateLocalization318.map R
    ((invert (R := R)).toRingHom.comp Polynomial.toLaurent) _ _
    (ContactRelativeInfinityLaurentPushout318.sections R c L) out

lemma infinity_coordinates_unit {r : ℕ}
    (out : infinitySections R c L →ₗ[Polynomial R] Fin r → Polynomial R) (x : infinitySections R c L) :
    invertVector R r (infinityCoordinates R c L out (infinityRestriction R c L x)) =
      fun i => Polynomial.toLaurent (out x i) := by
  rw [← ContactRelativeInfinityLaurentPushout318.sections_unit]
  have h := OriginalPolynomialCoordinateLocalization318.unit R
    ((invert (R := R)).toRingHom.comp Polynomial.toLaurent) _ _
    (ContactRelativeInfinityLaurentPushout318.sections R c L) out x
  change invertVector R r
    (OriginalPolynomialCoordinateLocalization318.map R _ _ _ _ out _ ) = _
  rw [h]
  ext i
  exact LaurentPolynomial.involutive_invert _

/-- The second bound uses the actual reciprocal coordinate, then inverts
back to the infinity polynomial variable. Both source charts remain whole. -/
theorem infinity_bound {r : ℕ}
    (out : infinitySections R c L →ₗ[Polynomial R] Fin r → Polynomial R) :
    ∃ b : ℕ, ∀ s : Γ(L.object,⊤),
      (fun i => Polynomial.toLaurent (out (ContactRelativeOriginalHZero318.pair R c L s).2 i)) ∈
        (upper (b : ℤ) : Submodule R (V R (Fin r))) := by
  let ψ : finiteSections R c L →+ V R (Fin r) := (invertVector R r).comp
    ((infinityCoordinates R c L out).toAddMonoidHom.comp
      (ContactOriginalRelativeOverlapSpan318.finiteMap R c L).toAddMonoidHom)
  have hp (p : Polynomial R) (x : finiteSections R c L) :
      ψ (p • x) = (invert (Polynomial.toLaurent p) : LaurentPolynomial R) • ψ x := by
    change invertVector R r (infinityCoordinates R c L out (finiteRestriction R c L (p • x))) = _
    rw [finite_polynomial,LinearMap.map_smul,invert_smul]
  obtain ⟨b,hb⟩ := ReciprocalImageUniformBound318.exists_bound R (finiteSections R c L)
    (V R (Fin r)) ψ hp (LinearMap.id : V R (Fin r) →ₗ[LaurentPolynomial R] V R (Fin r))
  refine ⟨b,fun s => ?_⟩
  have h := sub_eq_zero.mp (ContactRelativeOriginalHZero318.compatible R c L s)
  change finiteRestriction R c L (ContactRelativeOriginalHZero318.pair R c L s).1 =
    infinityRestriction R c L (ContactRelativeOriginalHZero318.pair R c L s).2 at h
  have hbs := hb (ContactRelativeOriginalHZero318.pair R c L s).1
  change invertVector R r (infinityCoordinates R c L out
    (finiteRestriction R c L (ContactRelativeOriginalHZero318.pair R c L s).1)) ∈ upper (b : ℤ) at hbs
  rw [h,infinity_coordinates_unit] at hbs
  exact hbs
end ContactRelativeGlobalCoordinateBounds318
