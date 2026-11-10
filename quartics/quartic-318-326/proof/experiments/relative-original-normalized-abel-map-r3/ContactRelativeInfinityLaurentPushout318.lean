module
public import ContactRelativeFiniteLaurentPushout318
public import ContactOriginalReciprocalRingEquivalence318
public section
noncomputable section
namespace ContactRelativeInfinityLaurentPushout318
open AlgebraicGeometry CategoryTheory LaurentPolynomial
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318
open scoped TensorProduct
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local instance : IsScalarTower ℚ (Polynomial ℚ) (infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ)
    (ContactOriginalReciprocalRingEquivalence318.positive c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

@[expose] def oldCoefficientEquivalence :
    R ⊗[ℚ] ContactOriginalReciprocalRingEquivalence318.positive c ≃ₐ[R] ring R c :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
    (ContactOriginalReciprocalRingEquivalence318.equivalence c)

/-- Coefficient extension preserves the genuine reciprocal scalar rule;
the old u-coordinate becomes t^-1 on the original common overlap. -/
lemma old_coefficient_scalar (l : LaurentPolynomial R) :
    oldCoefficientEquivalence R c (RelativeOriginalLaurentAlgebra318.laurentMap ℚ R
      (ContactOriginalReciprocalRingEquivalence318.positive c) l) =
    ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (invert l) := by
  induction l using LaurentPolynomial.induction_on' with
  | add l m hl hm => simp only [map_add,hl,hm]
  | C_mul_T z a =>
    rw [map_mul,map_mul,RelativeOriginalLaurentAlgebra318.laurentMap_C,
      RelativeOriginalLaurentAlgebra318.laurentMap_T]
    simp only [oldCoefficientEquivalence,Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul,AlgEquiv.refl_apply]
    rw [map_mul,invert_C,invert_T,RelativeOriginalLaurentAlgebra318.laurentMap_C,
      RelativeOriginalLaurentAlgebra318.laurentMap_T]
    congr 1
    · rw [map_one]
    · rw [ContactOriginalReciprocalRingEquivalence318.scalar,invert_T]

@[expose] def ringComparison :
    LaurentReciprocalTensor318.reciprocal R (R ⊗[ℚ] infinityRing c) ≃+* ring R c :=
  (LaurentReciprocalTensor318.equivalence R (R ⊗[ℚ] infinityRing c)).symm.trans
    ((RelativePolynomialLaurentPushout318.equivalence R (infinityRing c)).toRingEquiv.trans
      (oldCoefficientEquivalence R c).toRingEquiv)

/-- Both inversions are retained: source polynomial u acts as t^-1, and
the original infinity chart is mapped to the old finite-coordinate overlap.
Their composition preserves the actual common Laurent t action. -/
@[expose] def ringEquivalence :
    LaurentReciprocalTensor318.reciprocal R (R ⊗[ℚ] infinityRing c) ≃ₐ[LaurentPolynomial R] ring R c where
  __ := ringComparison R c
  commutes' l := by
    change oldCoefficientEquivalence R c (RelativePolynomialLaurentPushout318.equivalence R (infinityRing c)
      ((LaurentReciprocalTensor318.equivalence R (R ⊗[ℚ] infinityRing c)).symm
        (algebraMap (LaurentPolynomial R)
          (LaurentReciprocalTensor318.reciprocal R (R ⊗[ℚ] infinityRing c)) l))) = _
    rw [LaurentReciprocalTensor318.symm_tmul]
    change oldCoefficientEquivalence R c (RelativePolynomialLaurentPushout318.equivalence R (infinityRing c)
      (algebraMap (LaurentPolynomial R)
        (LaurentPolynomial R ⊗[Polynomial R] (R ⊗[ℚ] infinityRing c)) (invert l))) = _
    rw [(RelativePolynomialLaurentPushout318.equivalence R (infinityRing c)).commutes,
      old_coefficient_scalar,LaurentPolynomial.involutive_invert]
    rfl

lemma ringEquivalence_right (t : R ⊗[ℚ] infinityRing c) :
    ringEquivalence R c (letI := LaurentReciprocalTensor318.reciprocalAlgebra R;
      (1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] t) = infinityArrow R c t := by
  change oldCoefficientEquivalence R c (RelativePolynomialLaurentPushout318.equivalence R (infinityRing c)
    ((LaurentReciprocalTensor318.equivalence R (R ⊗[ℚ] infinityRing c)).symm _)) = _
  rw [LaurentReciprocalTensor318.symm_tmul,map_one,
    RelativePolynomialLaurentPushout318.equivalence_right]
  induction t using TensorProduct.inductionOn with
  | tmul r b =>
    change r ⊗ₜ[ℚ] ContactOriginalReciprocalRingEquivalence318.ringEquivalence c
      ((1 : LaurentPolynomial ℚ) ⊗ₜ[Polynomial ℚ] b) = r ⊗ₜ[ℚ] infinityMap c b
    rw [ContactOriginalReciprocalRingEquivalence318.right]
  | add x y hx hy => simp only [map_add,hx,hy]

variable (L : LineSheafClass318.Line (curve R c))
local instance : Algebra (Polynomial R) (LaurentPolynomial R) :=
  LaurentReciprocalTensor318.reciprocalAlgebra R
local instance : Algebra (R ⊗[ℚ] infinityRing c) (ring R c) := (infinityArrow R c).hom.toAlgebra
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

/-- Genuine reciprocal polynomial localization of the ORIGINAL infinity
section module, landing in the SAME whole overlap as the finite chart. -/
@[expose] def sections : LaurentPolynomial R ⊗[Polynomial R] infinitySections R c L ≃ₗ[LaurentPolynomial R]
    originalSections R c L :=
  OriginalAlgebraPushoutSections318.sections (Polynomial R) (LaurentPolynomial R)
    (R ⊗[ℚ] infinityRing c) (ring R c) (ringEquivalence R c) (ringEquivalence_right R c)
    (OriginalLineAffineModel318.sections _ (infinityLine R c L))
    (OriginalLineAffineModel318.sections _ (ContactOriginalRelativeLineOverlap318.line R c L))
    (OriginalAffineLinePathSections318.comparison (infinityArrow R c) (infinityLine R c L)
      (ContactOriginalRelativeLineOverlap318.line R c L) (infinityComparison R c L))

lemma sections_unit (x : infinitySections R c L) :
    sections R c L ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x) = infinityRestriction R c L x := by
  rw [OriginalAlgebraPushoutSections318.sections_unit]
  exact infinity_unit R c L x
end ContactRelativeInfinityLaurentPushout318
