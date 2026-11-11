module
public import RelativePolynomialLaurentPushout318
public import ContactOriginalFiniteRingSpan318
public import ContactOriginalRelativeLineOverlap318
public import OriginalAlgebraPushoutSections318
public section
noncomputable section
namespace ContactRelativeFiniteLaurentPushout318
open AlgebraicGeometry CategoryTheory
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318
open scoped TensorProduct
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local instance : IsScalarTower ℚ (Polynomial ℚ) (finiteRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- The actual old finite chart arrow, not just its coordinate image. -/
lemma old_map : finiteMap c =
    (Algebra.TensorProduct.includeRight (R := Polynomial ℚ)
      (A := LaurentPolynomial ℚ) (B := finiteRing c)).restrictScalars ℚ := by
  ext b
  exact RingHom.congr_fun (ContactOriginalFiniteRingSpan318.old_finite_map c) b

@[expose] def ringEquivalence :
    LaurentPolynomial R ⊗[Polynomial R] (R ⊗[ℚ] finiteRing c) ≃ₐ[LaurentPolynomial R] ring R c :=
  RelativePolynomialLaurentPushout318.equivalence R (finiteRing c)

lemma ringEquivalence_right (t : R ⊗[ℚ] finiteRing c) :
    ringEquivalence R c ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] t) = finiteArrow R c t := by
  rw [RelativePolynomialLaurentPushout318.equivalence_right]
  change Algebra.TensorProduct.map (AlgHom.id ℚ R) _ t =
    Algebra.TensorProduct.map (AlgHom.id ℚ R) (finiteMap c) t
  rw [old_map]

variable (L : LineSheafClass318.Line (curve R c))
local instance : Algebra (R ⊗[ℚ] finiteRing c) (ring R c) := (finiteArrow R c).hom.toAlgebra
local instance : Module (Polynomial R) (finiteSections R c L) := inferInstance
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

/-- The ACTUAL original finite restriction is a genuine Laurent
localization of the whole polynomial module, not merely Laurent-spanning. -/
@[expose] def sections : LaurentPolynomial R ⊗[Polynomial R] finiteSections R c L ≃ₗ[LaurentPolynomial R]
    originalSections R c L :=
  OriginalAlgebraPushoutSections318.sections (Polynomial R) (LaurentPolynomial R)
    (R ⊗[ℚ] finiteRing c) (ring R c) (ringEquivalence R c) (ringEquivalence_right R c)
    (OriginalLineAffineModel318.sections _ (finiteLine R c L))
    (OriginalLineAffineModel318.sections _ (ContactOriginalRelativeLineOverlap318.line R c L))
    (OriginalAffineLinePathSections318.comparison (finiteArrow R c) (finiteLine R c L)
      (ContactOriginalRelativeLineOverlap318.line R c L) (finiteComparison R c L))

lemma sections_unit (x : finiteSections R c L) :
    sections R c L ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x) = finiteRestriction R c L x := by
  rw [OriginalAlgebraPushoutSections318.sections_unit]
  exact finite_unit R c L x
end ContactRelativeFiniteLaurentPushout318
