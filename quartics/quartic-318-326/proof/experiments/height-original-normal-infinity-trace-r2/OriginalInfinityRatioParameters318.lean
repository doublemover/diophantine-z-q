module
public import FourRootRatioOrder318
public import DVRNormalizedInfinityOrder318
public import FourRootUnitScale318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace OriginalInfinityRatioParameters318
open Polynomial FourRootRatioOrder318
open scoped TensorProduct
variable (V : Type*) [CommRing V] (d a : Fin 4 → V)

/-- Only the nonvanishing factor of the first reciprocal radicand is
inverted. The reciprocal coordinate itself remains an integral parameter. -/
@[expose] def denominator : V[X] := C (d 0)*(1-C (a 0)*X)
abbrev Base := Localization.Away (denominator V d a)
@[expose] def denominatorUnit : (Base V d a)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S:=Base V d a) (denominator V d a)).unit
lemma denominatorUnit_value : (denominatorUnit V d a : Base V d a)=
    algebraMap V[X] (Base V d a) (denominator V d a) :=
  (IsLocalization.Away.algebraMap_isUnit (S:=Base V d a) (denominator V d a)).unit_spec
@[expose] def coordinate : Base V d a := algebraMap V[X] (Base V d a) X
@[expose] def common : Base V d a :=
  algebraMap V[X] (Base V d a) (DVRNormalizedInfinityOrder318.coefficient V d a 0)
@[expose] def ratios (i : Fin 3) : Base V d a :=
  algebraMap V[X] (Base V d a) (C (d i.succ)*(1-C (a i.succ)*X))*
    (↑(denominatorUnit V d a)⁻¹ : Base V d a)

lemma common_eq : common V d a=(denominatorUnit V d a : Base V d a)*coordinate V d a := by
  rw [common,coordinate,denominatorUnit_value,←map_mul]
  congr 1
  unfold DVRNormalizedInfinityOrder318.coefficient denominator
  ring

/-- Exact cancellation of the common reciprocal factor BEFORE dividing by
the reciprocal coordinate; valid on the whole chosen integral base. -/
lemma parameter (i : Fin 4) :
    original (common V d a) (ratios V d a) i=
      algebraMap V[X] (Base V d a) (DVRNormalizedInfinityOrder318.coefficient V d a i) := by
  refine Fin.cases rfl (fun i => ?_) i
  change common V d a*ratios V d a i = _
  rw [common_eq,ratios]
  calc
    _ = coordinate V d a *
      algebraMap V[X] (Base V d a) (C (d i.succ)*(1-C (a i.succ)*X)) *
        ((denominatorUnit V d a : Base V d a)*(↑(denominatorUnit V d a)⁻¹ : Base V d a)) := by ring
    _ = _ := by
      rw [Units.mul_inv,mul_one,coordinate,←map_mul]
      congr 1
      unfold DVRNormalizedInfinityOrder318.coefficient
      ring

/-- The exact base-changed original four-root order, not a relabeled
normalization, is identified through a full marked-root equivalence. -/
@[expose] def originalEquiv :
    FourRootOrder318.Order (fun i => algebraMap V[X] (Base V d a)
      (DVRNormalizedInfinityOrder318.coefficient V d a i)) ≃ₐ[Base V d a]
    OriginalOrder (common V d a) (ratios V d a) :=
  FourRootUnitScale318.four (original (common V d a) (ratios V d a))
    (fun i => algebraMap V[X] (Base V d a) (DVRNormalizedInfinityOrder318.coefficient V d a i)) 1
    (by intro i; simpa using (parameter V d a i).symm)

/-- Actual tensor base change of the original reciprocal order. -/
@[expose] def baseChangeEquiv :
    Base V d a ⊗[V[X]] DVRNormalizedInfinityOrder318.Order V d a ≃ₐ[Base V d a]
      OriginalOrder (common V d a) (ratios V d a) :=
  (FourRootOrder318.baseChange (DVRNormalizedInfinityOrder318.coefficient V d a) (Base V d a)).trans
    (originalEquiv V d a)
end OriginalInfinityRatioParameters318
