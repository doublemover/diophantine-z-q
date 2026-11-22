module
public import ActualGaussianWeberOriginalUniformization318
public import ActualGaussianComplexTorusKernel318
public section
noncomputable section

namespace ActualGaussianWeberLiteralComplexTorsion318

open ActualGaussianComplexTorusKernel318
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberComplexUniformizationFibres318

attribute [local instance] Classical.decEq

/-- Every class of the literal integer-generated Gaussian ideal has a
representative in the two actual ZMod coordinate boxes. Finite size,
not exact size, suffices to construct the full torsion field. -/
theorem gaussian_integer_quotient_finite (M : ℕ) (hM : 0 < M) :
    Finite (GaussianInt ⧸ Ide (M:GaussianInt)) := by
  letI : NeZero M := ⟨hM.ne'⟩
  let repr (b : ZMod M × ZMod M) : GaussianInt ⧸ Ide (M:GaussianInt) :=
    Ideal.Quotient.mk (Ide (M:GaussianInt)) (literal (b.1.val:ℤ) (b.2.val:ℤ))
  apply Finite.of_surjective repr
  intro c
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
  let x : ZMod M := z.re
  let y : ZMod M := z.im
  refine ⟨(x,y), ?_⟩
  have hres (a : ℤ) : (M:ℤ) ∣ a - (((a:ZMod M).val:ℕ):ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨s, hs⟩ := hres z.re
  obtain ⟨t, ht⟩ := hres z.im
  symm
  apply (Ideal.Quotient.eq (I := Ide (M:GaussianInt))).mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨literal s t, ?_⟩
  apply Zsqrtd.ext
  · simpa only [repr, x, literal, Zsqrtd.re_sub, Zsqrtd.re_mul,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, mul_zero, zero_mul, add_zero] using hs
  · simpa only [repr, y, literal, Zsqrtd.im_sub, Zsqrtd.im_mul,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, mul_zero, zero_mul, add_zero, zero_add] using ht

private theorem scalar_nat (M : ℕ) (P : Torus) :
    scalar (M:GaussianInt) P = M • P := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective lattice P
  rw [scalar_on, map_natCast, ←nsmul_eq_mul, map_nsmul]

/-- Same native positive-i dictionary yields finiteness of the exact
complex M-torsion points used by the actual full torsion field. No
field-of-definition, algebraicity, or rank hypothesis enters. -/
theorem literal_complex_torsion_finite (U : OriginalUniformization) (M : ℕ) (hM : 0 < M) :
    Finite {P : WP ℂ // M • P = 0} := by
  letI : Finite (GaussianInt ⧸ Ide (M:GaussianInt)) := gaussian_integer_quotient_finite M hM
  have h0 : (M:GaussianInt) ≠ 0 := by exact_mod_cast hM.ne'
  let E := kernel_equiv (M:GaussianInt) h0
  let phi (P : {P : WP ℂ // M • P = 0}) : {Q : Torus // scalar (M:GaussianInt) Q = 0} :=
    ⟨U.point.symm P.val, by
      rw [scalar_nat, ←map_nsmul, P.property, map_zero]⟩
  have hp : Function.Injective phi := by
    intro P Q h
    apply Subtype.ext
    exact U.point.symm.injective (congrArg Subtype.val h)
  exact Finite.of_injective (E.symm ∘ phi) (E.symm.injective.comp hp)

end ActualGaussianWeberLiteralComplexTorsion318
