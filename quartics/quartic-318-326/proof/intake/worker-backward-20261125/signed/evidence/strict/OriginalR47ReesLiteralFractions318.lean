module
public import OriginalAffineReesChartLocal318
public section
noncomputable section

namespace OriginalR47ReesLiteralFractions318

open Polynomial HomogeneousLocalization
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
open OriginalAffineReesChartLocal318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (a : R) (ha : a ∈ I)

/-- A numerator in the actual power of the center ideal, not an abstract
fraction in an auxiliary field. This holds before and after any flat
étale coefficient extension, even if the coefficient ring is not a domain. -/
theorem exists_ratio (z : chart I a ha) :
    ∃ n : ℕ, ∃ r : ↥(I^n), ratio I a ha n r = z := by
  obtain ⟨n,w,hw,he⟩ := Away.mk_surjective (grade I) (generator_grade I a ha) z
  have hw' : w ∈ grade I n := by simpa only [Nat.nsmul_eq_mul, mul_one] using hw
  let r : ↥(I^n) := ⟨w.val.coeff n, w.property n⟩
  have hr : (homogeneous I n r.val r.property).val = w := by
    apply Subtype.ext
    exact (homogeneous_value I hw').symm
  refine ⟨n,r,?_⟩
  rw [← he]
  apply HomogeneousLocalization.val_injective _
  simp only [ratio, Away.val_mk, hr]

/-- Literal reading of the Proj chart as fractions with denominator a. -/
theorem chartEval_ratio (n : ℕ) (r : ↥(I^n)) :
    chartEval I a ha (ratio I a ha n r) =
      IsLocalization.mk' (Localization.Away a) r.val
        (⟨a^n, n, rfl⟩ : Submonoid.powers a) := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  have he := congrArg (chartEval I a ha) (clear_ratio I a ha n r)
  have hm := (chartEval I a ha).map_mul (ratio I a ha n r) ((chartScalars I a ha a)^n)
  have hp := (chartEval I a ha).map_pow (chartScalars I a ha a) n
  rw [hm, hp, chartEval_scalar I a ha a, chartEval_scalar I a ha r.val] at he
  change chartEval I a ha (ratio I a ha n r) *
    (algebraMap R (Localization.Away a)) (a^n) = (algebraMap R (Localization.Away a)) r.val
  rw [(algebraMap R (Localization.Away a)).map_pow]
  exact he

/-- No domain or nonzero-generator assumption is needed. Vanishing of
r/a^n supplies a^k r=0, and this same k kills the homogeneous numerator
after multiplication by (aT)^k in the actual Rees algebra. -/
theorem ratio_zero_of_chartEval_zero (n : ℕ) (r : ↥(I^n))
    (h : chartEval I a ha (ratio I a ha n r) = 0) :
    ratio I a ha n r = 0 := by
  rw [chartEval_ratio I a ha] at h
  obtain ⟨⟨m,⟨k,hk⟩⟩,hm⟩ :=
    (IsLocalization.mk'_eq_zero_iff (S := Localization.Away a)
      r.val (⟨a^n, n, rfl⟩ : Submonoid.powers a)).mp h
  have hz : a^k * r.val = 0 := by simpa only [Subtype.coe_mk, hk] using hm
  apply HomogeneousLocalization.val_injective _
  rw [ratio, Away.val_mk, Localization.mk_eq_mk', val_zero]
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  refine ⟨⟨(generator I a ha)^k, k, rfl⟩, ?_⟩
  apply Subtype.ext
  change (monomial 1 a)^k * monomial n r.val = (0 : R[X])
  rw [monomial_pow, monomial_mul_monomial, hz, monomial_zero_right]

/-- The faithful affine target for the flat base-change comparison. -/
theorem chartEval_injective : Function.Injective (chartEval I a ha) := by
  intro x y h
  have hz : chartEval I a ha (x-y) = 0 :=
    ((chartEval I a ha).map_sub x y).trans (sub_eq_zero.mpr h)
  obtain ⟨n,r,hr⟩ := exists_ratio I a ha (x-y)
  rw [← hr] at hz
  exact sub_eq_zero.mp (hr.symm.trans (ratio_zero_of_chartEval_zero I a ha n r hz))

end OriginalR47ReesLiteralFractions318

#print axioms OriginalR47ReesLiteralFractions318.exists_ratio
#print axioms OriginalR47ReesLiteralFractions318.chartEval_ratio
#print axioms OriginalR47ReesLiteralFractions318.ratio_zero_of_chartEval_zero
#print axioms OriginalR47ReesLiteralFractions318.chartEval_injective
