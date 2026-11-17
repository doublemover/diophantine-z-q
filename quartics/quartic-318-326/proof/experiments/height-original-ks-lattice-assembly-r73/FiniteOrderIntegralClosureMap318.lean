module
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public section
noncomputable section
namespace FiniteOrderIntegralClosureMap318
variable {R B L : Type*} [CommRing R] [CommRing B] [Field L]
  [Algebra R B] [Algebra R L] [Module.Finite R B]
variable (f : B →ₐ[R] L) (hf : Function.Injective f)

/-- This algebra is explicitly selected by the supplied map; f is not
registered as an uninferable global instance parameter. -/
@[expose] def fieldAlgebra : Algebra B L := f.toRingHom.toAlgebra

include hf in
/-- Finite-order integrality is transported by the actual injective algebra map. -/
theorem image_integral (b : B) : IsIntegral R (f b) :=
  (isIntegral_algHom_iff f hf).2 (IsIntegral.of_finite R b)

/-- The image is the same element of L, now certified integral over R. -/
@[expose] def toClosure : B →ₐ[R] integralClosure R L where
  toFun b := ⟨f b, image_integral f hf b⟩
  map_one' := Subtype.ext (map_one f)
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f a b)
  map_mul' a b := Subtype.ext (map_mul f a b)
  commutes' r := Subtype.ext (f.commutes r)

@[simp] theorem toClosure_val (b : B) : (toClosure f hf b).val = f b := rfl

theorem toClosure_injective : Function.Injective (toClosure f hf) := by
  intro a b h
  apply hf
  have hv := congrArg (fun z : integralClosure R L => z.val) h
  simpa only [toClosure_val] using hv

/-- The compatibility is derived from f.commutes for its three named
Algebra projections, not postulated for an unrelated native scalar action. -/
theorem field_scalar_tower :
    letI := fieldAlgebra f
    @IsScalarTower R B L (inferInstance : Algebra R B).toSMul
      (fieldAlgebra f).toSMul (inferInstance : Algebra R L).toSMul := by
  letI := fieldAlgebra f
  exact IsScalarTower.of_algebraMap_eq (R := R) (S := B) (A := L)
    (fun r => (f.commutes r).symm)

/-- With the supplied action, integrality over the finite order is exactly
integrality over its coefficient ring. No integrally-closed order premise. -/
theorem integral_iff (x : L) :
    letI := fieldAlgebra f
    IsIntegral B x ↔ IsIntegral R x := by
  letI := fieldAlgebra f
  letI := field_scalar_tower f
  exact ⟨fun h => isIntegral_trans (R := R) x h, fun h => h.tower_top⟩

/-- The literal R-integral closure inside L is also the integral closure
of the specified order. A fraction-field identification is a separate theorem. -/
theorem isIntegralClosure :
    letI := fieldAlgebra f
    IsIntegralClosure (integralClosure R L) B L := by
  letI := fieldAlgebra f
  exact
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := by
        intro x
        rw [integral_iff f]
        exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩ }

/-- The explicit order-to-closure algebra, for later map finiteness proofs.
No finiteness of this closure has been asserted here. -/
@[expose] def closureAlgebra : Algebra B (integralClosure R L) :=
  (toClosure f hf).toRingHom.toAlgebra

end FiniteOrderIntegralClosureMap318
