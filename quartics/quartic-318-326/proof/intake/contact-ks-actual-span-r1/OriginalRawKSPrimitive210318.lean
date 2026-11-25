module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
The integral primitive Hodge-square map for the original discriminant 210.
The input map is the genuine raw KS on the original arithmetic fine family.
Yuan, Thm. 1.1 supplies its injectivity and exact image. We construct the
primitive map before any scalar change, not by dividing on a special fibre.
-/

@[expose] public section

open scoped TensorProduct

namespace OriginalRawKSPrimitive210318

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- Multiplication on the literal dualizing-square module. -/
def scale210 : N →ₗ[R] N := (210 : R) • LinearMap.id

variable (raw : M →ₗ[R] N)
  (rawInj : Function.Injective raw)
  (regular210 : Function.Injective (scale210 : N →ₗ[R] N))
  (exactImage : LinearMap.range raw = LinearMap.range (scale210 : N →ₗ[R] N))

/-- No generators are chosen for either line. -/
noncomputable def primitive : M ≃ₗ[R] N :=
  (LinearEquiv.ofInjective raw rawInj).trans
    ((LinearEquiv.ofEq _ _ exactImage).trans
      (LinearEquiv.ofInjective scale210 regular210).symm)

theorem scalar_on_original (m : M) :
    (210 : R) • primitive raw rawInj regular210 exactImage m = raw m := by
  change scale210
    ((LinearEquiv.ofInjective scale210 regular210).symm
      (LinearEquiv.ofEq _ _ exactImage (LinearEquiv.ofInjective raw rawInj m))) = raw m
  rw [LinearEquiv.ofInjective_symm_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

theorem raw_is_scaled :
    raw = (210 : R) • (primitive raw rawInj regular210 exactImage).toLinearMap := by
  apply LinearMap.ext
  intro m
  exact (scalar_on_original raw rawInj regular210 exactImage m).symm

section ScalarChange

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The same primitive map over the actual point or residue ring.
No regularity hypothesis on the image of 210 in S is made. -/
noncomputable def changed : (S ⊗[R] M) ≃ₗ[S] (S ⊗[R] N) :=
  (primitive raw rawInj regular210 exactImage).baseChange R S M N

theorem changed_raw :
    raw.baseChange S = (210 : S) •
      (changed raw rawInj regular210 exactImage S).toLinearMap := by
  let f := (primitive raw rawInj regular210 exactImage).toLinearMap
  calc
    raw.baseChange S = ((210 : R) • f).baseChange S :=
      congrArg (LinearMap.baseChange S) (raw_is_scaled raw rawInj regular210 exactImage)
    _ = (210 : S) • (changed raw rawInj regular210 exactImage S).toLinearMap := by
      rw [LinearMap.baseChange_smul]
      apply LinearMap.ext
      intro z
      change (210 : R) • (f.baseChange S z) = (210 : S) • (f.baseChange S z)
      have hr := Nat.cast_smul_eq_nsmul R 210 (f.baseChange S z)
      have hs := Nat.cast_smul_eq_nsmul S 210 (f.baseChange S z)
      simpa only [Nat.cast_ofNat] using hr.trans hs.symm

/-- Pull a given exact dualizing-square section into the actual Hodge-square module. -/
noncomputable def pullSection (q : S ⊗[R] N) : S ⊗[R] M :=
  (changed raw rawInj regular210 exactImage S).symm q

theorem section_primitive (q : S ⊗[R] N) :
    changed raw rawInj regular210 exactImage S
      (pullSection raw rawInj regular210 exactImage S q) = q :=
  LinearEquiv.apply_symm_apply _ _

theorem section_raw (q : S ⊗[R] N) :
    raw.baseChange S (pullSection raw rawInj regular210 exactImage S q) = (210 : S) • q := by
  rw [changed_raw raw rawInj regular210 exactImage S]
  change (210 : S) • (changed raw rawInj regular210 exactImage S
      (pullSection raw rawInj regular210 exactImage S q)) = _
  rw [section_primitive]

include rawInj regular210 exactImage in
theorem raw_zero_in_bad_residue (h : (210 : S) = 0) :
    raw.baseChange S = 0 := by
  rw [changed_raw raw rawInj regular210 exactImage S, h, zero_smul]

end ScalarChange

end OriginalRawKSPrimitive210318

#print axioms OriginalRawKSPrimitive210318.scalar_on_original
#print axioms OriginalRawKSPrimitive210318.changed_raw
#print axioms OriginalRawKSPrimitive210318.section_raw
#print axioms OriginalRawKSPrimitive210318.raw_zero_in_bad_residue
