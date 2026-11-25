module
public import OriginalAffineReesBlowup318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section

namespace OriginalAffineReesChartLocal318

open Polynomial HomogeneousLocalization
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (a : R) (ha : a ∈ I)

abbrev full := Localization.Away (generator I a ha)

private theorem val_scalar (r : R) :
    (chartScalars I a ha r).val = algebraMap (Rees I) (full I a ha)
      (algebraMap R (Rees I) r) := by
  change Localization.mk (algebraMap R (Rees I) r) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- Equality in the actual Rees algebra, before any localization. -/
theorem numerator_clear (n : ℕ) (w : Rees I) (hw : w ∈ grade I n) :
    (algebraMap R (Rees I) a)^n * w =
      algebraMap R (Rees I) (w.val.coeff n) * (generator I a ha)^n := by
  apply Subtype.ext
  change C a ^ n * w.val = C (w.val.coeff n) * monomial 1 a ^ n
  let r := w.val.coeff n
  calc
    C a ^ n * w.val = C a ^ n * monomial n r :=
      congrArg (fun z : R[X] => C a ^ n * z) (homogeneous_value I hw)
    _ = C r * monomial 1 a ^ n := by
      simp only [← monomial_zero_left, monomial_pow, zero_mul, one_mul,
        monomial_mul_monomial, zero_add]
      rw [mul_comm (a ^ n) r]

/-- Every degree-zero fraction is a genuine ratio r/a^n, in the
precise sense of this equality inside the actual chart ring. -/
theorem clear (z : chart I a ha) :
    ∃ n : ℕ, ∃ r : R, z * (chartScalars I a ha a)^n = chartScalars I a ha r := by
  obtain ⟨n,w,hw,he⟩ := Away.mk_surjective (grade I) (generator_grade I a ha) z
  have hw' : w ∈ grade I n := by simpa only [Nat.nsmul_eq_mul, mul_one] using hw
  let s : Submonoid.powers (generator I a ha) := ⟨(generator I a ha)^n, n, rfl⟩
  refine ⟨n,w.val.coeff n, ?_⟩
  apply HomogeneousLocalization.val_injective _
  rw [← he, val_mul, val_pow, Away.val_mk, val_scalar, val_scalar, ← map_pow]
  change Localization.mk w s * algebraMap (Rees I) (full I a ha) ((algebraMap R (Rees I) a)^n) = _
  rw [Localization.mk_eq_mk', mul_comm (IsLocalization.mk' (full I a ha) w s),
    IsLocalization.mul_mk'_eq_mk'_of_mul,
    numerator_clear I a ha n w hw']
  exact IsLocalization.mk'_mul_cancel_right (S := full I a ha) _ s

/-- Evaluate the ambient indeterminate at 1, only after localizing
the real base at a. -/
@[expose] def evaluation : Rees I →+* Localization.Away a :=
  (algebraMap R (Localization.Away a)).comp
    ((Polynomial.evalRingHom 1).comp (Subalgebra.val (reesAlgebra I)).toRingHom)

theorem eval_gen : evaluation I a (generator I a ha) =
    algebraMap R (Localization.Away a) a := by
  change algebraMap R (Localization.Away a) (eval 1 (monomial 1 a)) = _
  simp

@[expose] def fullEval : full I a ha →+* Localization.Away a :=
  IsLocalization.Away.lift (g := evaluation I a) (generator I a ha)
    (by rw [eval_gen I a ha]; exact IsLocalization.Away.algebraMap_isUnit a)

@[expose] def chartEval : chart I a ha →+* Localization.Away a :=
  (fullEval I a ha).comp (algebraMap (chart I a ha) (full I a ha))

@[simp] theorem chartEval_scalar (r : R) :
    chartEval I a ha (chartScalars I a ha r) = algebraMap R (Localization.Away a) r := by
  change fullEval I a ha (chartScalars I a ha r).val = _
  rw [val_scalar, fullEval, IsLocalization.Away.lift_eq]
  change algebraMap R (Localization.Away a) (eval 1 (C r)) = _
  rw [eval_C]

/-- The actual numerator rT^n over the actual chosen denominator (aT)^n. -/
@[expose] def ratio (n : ℕ) (r : ↥(I^n)) : chart I a ha :=
  Away.mk (grade I) (generator_grade I a ha) n (homogeneous I n r.val r.property).val
    (by simpa only [Nat.nsmul_eq_mul, mul_one] using (homogeneous I n r.val r.property).property)

theorem clear_ratio (n : ℕ) (r : ↥(I^n)) :
    ratio I a ha n r * (chartScalars I a ha a)^n = chartScalars I a ha r.val := by
  let w : Rees I := (homogeneous I n r.val r.property).val
  let s : Submonoid.powers (generator I a ha) := ⟨(generator I a ha)^n, n, rfl⟩
  apply HomogeneousLocalization.val_injective _
  rw [ratio, val_mul, val_pow, Away.val_mk, val_scalar, val_scalar, ← map_pow]
  change Localization.mk w s * algebraMap (Rees I) (full I a ha) ((algebraMap R (Rees I) a)^n) = _
  rw [Localization.mk_eq_mk', mul_comm (IsLocalization.mk' (full I a ha) w s),
    IsLocalization.mul_mk'_eq_mk'_of_mul,
    numerator_clear I a ha n w (homogeneous I n r.val r.property).property]
  have hcoeff : w.val.coeff n = r.val := by
    change (monomial n r.val).coeff n = r.val
    exact coeff_monomial_same n r.val
  rw [hcoeff]
  exact IsLocalization.mk'_mul_cancel_right (S := full I a ha) _ s

/-- The exact degree-one overlap element in Mathlib Proj is the
old coordinate ratio, on the very same localization chart. -/
theorem degree_one_overlap (b : R) (hb : b ∈ I) :
    Away.isLocalizationElem (generator_grade I a ha) (generator_grade I b hb) =
      ratio I a ha 1 ⟨b,by simpa only [pow_one] using hb⟩ := by
  change Away.mk (grade I) (generator_grade I a ha) 1 ((generator I b hb)^1) _ = _
  simp only [pow_one, ratio, generator]

end OriginalAffineReesChartLocal318

#print axioms OriginalAffineReesChartLocal318.clear
#print axioms OriginalAffineReesChartLocal318.chartEval_scalar
#print axioms OriginalAffineReesChartLocal318.clear_ratio
#print axioms OriginalAffineReesChartLocal318.degree_one_overlap
