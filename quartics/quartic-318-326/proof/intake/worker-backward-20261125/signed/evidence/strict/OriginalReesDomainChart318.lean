module
public import OriginalAffineReesChartLocal318
public section
noncomputable section

namespace OriginalReesDomainChart318

open Polynomial HomogeneousLocalization
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
open OriginalAffineReesChartLocal318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R] [IsDomain R]
variable (I : Ideal R) (a : R) (ha : a ∈ I) (hn : a ≠ 0)

include hn in
omit [IsDomain R] in
theorem denom_ne_zero : generator I a ha ≠ 0 := by
  intro h
  have hP := congrArg (fun z : Rees I => z.val.coeff 1) h
  change (monomial 1 a).coeff 1 = (0 : R[X]).coeff 1 at hP
  rw [coeff_monomial_same, coeff_zero] at hP
  exact hn hP

include hn in
theorem chart_isDomain : IsDomain (chart I a ha) := by
  let : IsDomain (Localization.Away (generator I a ha)) :=
    Localization.Away.isDomain (denom_ne_zero I a ha hn)
  let j : chart I a ha →+* Localization.Away (generator I a ha) := algebraMap _ _
  have hj : Function.Injective j := by
    intro x y h
    change x.val = y.val at h
    exact HomogeneousLocalization.val_injective (Submonoid.powers (generator I a ha)) h
  exact Function.Injective.isDomain j hj

include hn in
theorem base_local_injective : Function.Injective (algebraMap R (Localization.Away a)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn)

include hn in
theorem scalar_ne : chartScalars I a ha a ≠ 0 := by
  intro h
  have e := congrArg (chartEval I a ha) h
  rw [chartEval_scalar, map_zero] at e
  exact hn ((base_local_injective a hn) (e.trans (map_zero _).symm))

include hn in
/-- The literal homogeneous-chart power of the base scalar is nonzero.
Transport it into the full localization before applying ordinary domain
power cancellation. -/
theorem scalar_pow_ne (n : ℕ) : (chartScalars I a ha a)^n ≠ 0 := by
  let : IsDomain (Localization.Away (generator I a ha)) :=
    Localization.Away.isDomain (denom_ne_zero I a ha hn)
  let v : chart I a ha → Localization.Away (generator I a ha) :=
    fun z => HomogeneousLocalization.val z
  have hval : v (chartScalars I a ha a) ≠ 0 := by
    intro he
    apply scalar_ne I a ha hn
    exact (HomogeneousLocalization.val_injective (Submonoid.powers (generator I a ha)))
      (he.trans HomogeneousLocalization.val_zero.symm)
  intro he
  have hp := congrArg v he
  change ((chartScalars I a ha a)^n).val = (0 : chart I a ha).val at hp
  rw [val_pow, val_zero] at hp
  exact (pow_ne_zero n hval) hp

include hn in
/-- Cancel a power of the actual chart denominator by evaluating into
the faithful full localization, without changing the chart operations. -/
theorem cancel_scalar_pow (n : ℕ) {x y : chart I a ha}
    (h : x * (chartScalars I a ha a)^n = y * (chartScalars I a ha a)^n) :
    x = y := by
  let : IsDomain (Localization.Away (generator I a ha)) :=
    Localization.Away.isDomain (denom_ne_zero I a ha hn)
  have hNonzero : (chartScalars I a ha a).val ^ n ≠ 0 := by
    intro he
    apply scalar_pow_ne I a ha hn n
    apply HomogeneousLocalization.val_injective (Submonoid.powers (generator I a ha))
    rw [val_pow, val_zero]
    exact he
  have hV : x.val * (chartScalars I a ha a).val ^ n =
      y.val * (chartScalars I a ha a).val ^ n := by
    have e := congrArg (fun z : chart I a ha => z.val) h
    simpa only [val_mul, val_pow] using e
  exact HomogeneousLocalization.val_injective (Submonoid.powers (generator I a ha))
    (mul_right_cancel₀ hNonzero hV)

include hn in
/-- Exact cancellation in a genuine domain chart. This is the injective
read needed for the three literal thin/thick node presentations; a reduced
incidence ring with an extra component cannot pass the same argument. -/
theorem chart_eval_injective : Function.Injective (chartEval I a ha) := by
  let m := chartScalars I a ha
  let f := chartEval I a ha
  intro x y hxy
  change f x = f y at hxy
  have h0 : f (x-y) = 0 := (f.map_sub x y).trans (sub_eq_zero.mpr hxy)
  obtain ⟨d,r,hr⟩ := OriginalAffineReesChartLocal318.clear I a ha (x-y)
  have hs : f ((x-y) * (m a)^d) = f (m r) := congrArg (fun z : chart I a ha => f z) hr
  have hs0 : f (m r) = 0 := hs.symm.trans
    ((f.map_mul (x-y) ((m a)^d)).trans (by rw [h0,zero_mul]))
  have hread : (algebraMap R (Localization.Away a)) r = 0 :=
    (chartEval_scalar I a ha r).symm.trans hs0
  have hz : r=0 := (base_local_injective a hn) (hread.trans (map_zero _).symm)
  have hprod : (x-y) * (m a)^d = 0 :=
    hr.trans ((congrArg (fun z : R => m z) hz).trans m.map_zero)
  have hright : (0 : chart I a ha) * (m a)^d = 0 := by
    apply HomogeneousLocalization.val_injective (Submonoid.powers (generator I a ha))
    simp only [val_mul, val_zero, zero_mul]
  have hcancel : (x-y) * (m a)^d = (0 : chart I a ha) * (m a)^d :=
    hprod.trans hright.symm
  have hz' : x-y = (0 : chart I a ha) := cancel_scalar_pow I a ha hn d hcancel
  apply HomogeneousLocalization.val_injective (Submonoid.powers (generator I a ha))
  have hv := congrArg (fun z : chart I a ha => z.val) hz'
  change (x-y).val = (0 : chart I a ha).val at hv
  rw [val_sub, val_zero] at hv
  exact sub_eq_zero.mp hv

end OriginalReesDomainChart318

#print axioms OriginalReesDomainChart318.chart_isDomain
#print axioms OriginalReesDomainChart318.chart_eval_injective
#print axioms OriginalReesDomainChart318.scalar_ne
#print axioms OriginalReesDomainChart318.scalar_pow_ne
#print axioms OriginalReesDomainChart318.cancel_scalar_pow
