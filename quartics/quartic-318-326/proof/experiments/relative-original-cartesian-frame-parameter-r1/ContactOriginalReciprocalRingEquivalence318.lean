module
public import ContactOriginalInfinityRingSpan318
public import AffineSpecOriginalRingEquivalence318
public import LaurentReciprocalTensor318
public section
noncomputable section
namespace ContactOriginalReciprocalRingEquivalence318
open AlgebraicGeometry CategoryTheory LaurentPolynomial
open ContactOriginalRelativeOverlap318 ContactOriginalRelativePolynomialCharts318
open scoped TensorProduct
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
abbrev positive := LaurentPolynomial ℚ ⊗[Polynomial ℚ] infinityRing c

/-- The positive u-Laurent presentation of the original infinity chart
maps to the SAME old t-overlap by u=t^-1, through both actual chart isos. -/
@[expose] def ringEquivalence : positive c ≃+* oldRing c :=
  (LaurentReciprocalTensor318.equivalence ℚ (infinityRing c)).trans
    (AffineSpecOriginalRingEquivalence318.equivalence
      (ContactOriginalInfinityRingSpan318.comparison c))

lemma tmul (l : LaurentPolynomial ℚ) (b : infinityRing c) :
    ringEquivalence c (l ⊗ₜ[Polynomial ℚ] b) =
      algebraMap (LaurentPolynomial ℚ) (oldRing c) (invert l) * infinityMap c b := by
  rw [ringEquivalence,RingEquiv.trans_apply,LaurentReciprocalTensor318.tmul]
  exact ContactOriginalInfinityRingSpan318.transport_tmul c (invert l) b

lemma right (b : infinityRing c) :
    ringEquivalence c ((1 : LaurentPolynomial ℚ) ⊗ₜ[Polynomial ℚ] b) = infinityMap c b := by
  rw [tmul,map_one,map_one,one_mul]

lemma scalar (l : LaurentPolynomial ℚ) :
    ringEquivalence c (algebraMap (LaurentPolynomial ℚ) (positive c) l) =
      algebraMap (LaurentPolynomial ℚ) (oldRing c) (invert l) := by
  change ringEquivalence c (l ⊗ₜ[Polynomial ℚ] (1 : infinityRing c)) = _
  rw [tmul,map_one,mul_one]

@[expose] def equivalence : positive c ≃ₐ[ℚ] oldRing c where
  __ := ringEquivalence c
  commutes' q := RingHom.congr_fun (RingHom.ext_rat _ _) q
end ContactOriginalReciprocalRingEquivalence318
