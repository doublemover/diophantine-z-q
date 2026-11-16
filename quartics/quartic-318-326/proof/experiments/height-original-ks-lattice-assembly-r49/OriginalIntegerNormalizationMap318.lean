module
public import OriginalIntegerFiniteClosure318
public section
noncomputable section
namespace OriginalIntegerNormalizationMap318
open Polynomial
open scoped TensorProduct
open OriginalIntegerAffineModel318
attribute [local instance] OriginalIntegerAffineModel318.rationalPolynomialAlgebra
attribute [local instance] IntegerPolynomialFractionField318.fieldAlgebra
attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra
attribute [local instance] OriginalIntegerFractionField318.integerFieldAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev L := OriginalIntegerFiniteClosure318.L c
abbrev Closure := OriginalIntegerFiniteClosure318.Closure c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
local instance orderFinite : Module.Finite ℤ[X] (Order c) := (finite_free c).1

/-- The rational-fiber root scaling preserves the exact coefficient map. -/
theorem embedding_on_polynomial (p : ℤ[X]) :
    embedding c (algebraMap ℤ[X] (Order c) p) =
      algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) (algebraMap ℤ[X] ℚ[X] p) := by
  unfold embedding
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply ℤ[X] ℚ[X] (ℚ[X] ⊗[ℤ[X]] Order c)]
  exact (rationalFiber c).commutes _

/-- The two paths from Z[T] into the original field agree: through the
cleared integer order, or through the parameter field Q(T). -/
theorem fieldEmbedding_on_polynomial (p : ℤ[X]) :
    OriginalIntegerFractionField318.fieldEmbedding c (algebraMap ℤ[X] (Order c) p) =
      algebraMap ℤ[X] (L c) p := by
  change ContactKummerOrder318.embedding c
    (embedding c (algebraMap ℤ[X] (Order c) p)) = _
  rw [embedding_on_polynomial, SourceFractionField318.embedding_on_polynomial]
  rfl

@[expose] def fieldAlgHom : Order c →ₐ[ℤ[X]] L c :=
  { OriginalIntegerFractionField318.fieldEmbedding c with
    commutes' := fieldEmbedding_on_polynomial c }

theorem field_scalar_tower : @IsScalarTower ℤ[X] (Order c) (L c)
    (inferInstance : Algebra ℤ[X] (Order c)).toSMul
    (OriginalIntegerFractionField318.integerFieldAlgebra c).toSMul
    (OriginalIntegerFiniteClosure318.baseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq (fun p => (fieldEmbedding_on_polynomial c p).symm)

/-- Every element of the actual integer order belongs to the constructed
finite closure; this is derived from the monic finite order. -/
theorem image_integral (x : Order c) :
    IsIntegral ℤ[X] (OriginalIntegerFractionField318.fieldEmbedding c x) :=
  (isIntegral_algHom_iff (fieldAlgHom c)
    (OriginalIntegerFractionField318.fieldEmbedding_injective c)).2
      (IsIntegral.of_finite ℤ[X] x)

@[expose] def toClosure : Order c →ₐ[ℤ[X]] Closure c where
  toFun x := ⟨OriginalIntegerFractionField318.fieldEmbedding c x, image_integral c x⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  commutes' p := Subtype.ext (fieldEmbedding_on_polynomial c p)

theorem toClosure_injective : Function.Injective (toClosure c) := by
  intro x y h
  exact OriginalIntegerFractionField318.fieldEmbedding_injective c (congrArg Subtype.val h)

/-- Integrality over the monic order and over its integer parameter ring
are equivalent in this exact field. -/
theorem integral_iff (x : L c) : IsIntegral (Order c) x ↔ IsIntegral ℤ[X] x := by
  letI := field_scalar_tower c
  exact ⟨fun h => isIntegral_trans (R := ℤ[X]) x h, fun h => h.tower_top⟩

/-- The previously constructed finite normal closure really is the integral
closure of the original integer order in its actual fraction field. -/
theorem isIntegralClosure : IsIntegralClosure (Closure c) (Order c) (L c) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    rw [integral_iff]
    exact ⟨fun h => ⟨⟨x,h⟩,rfl⟩, fun ⟨y,hy⟩ => hy ▸ y.property⟩

@[expose] def closureAlgebra : Algebra (Order c) (Closure c) :=
  (toClosure c).toRingHom.toAlgebra
attribute [local instance] closureAlgebra

theorem closure_scalar_tower : IsScalarTower ℤ[X] (Order c) (Closure c) :=
  IsScalarTower.of_algebraMap_eq (fun p => ((toClosure c).commutes p).symm)

/-- The normalization map is finite over the actual original order, not
only finite over the parameter ring. -/
theorem finite_normalization : Module.Finite (Order c) (Closure c) := by
  letI : IsScalarTower ℤ[X] (Order c) (Closure c) := closure_scalar_tower c
  letI : Module.Finite ℤ[X] (Closure c) := OriginalIntegerFiniteClosure318.closure_finite c
  exact Module.Finite.of_restrictScalars_finite ℤ[X] (Order c) (Closure c)

end OriginalIntegerNormalizationMap318
