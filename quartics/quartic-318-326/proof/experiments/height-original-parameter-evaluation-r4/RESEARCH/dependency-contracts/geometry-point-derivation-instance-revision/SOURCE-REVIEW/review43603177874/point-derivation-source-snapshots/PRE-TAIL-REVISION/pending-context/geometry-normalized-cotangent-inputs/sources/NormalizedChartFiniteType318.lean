module
public import NormalizedValuativeChartStructure318
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public section
noncomputable section
namespace NormalizedChartFiniteType318
open Polynomial
universe u
variable (V : Type u) [CommRing V] (d a : Fin 4 → V)

/-- Actual whole finite order, including nonunit twists: finite over V[X]
implies finite type over V. No finite-type/model regularity premise is added. -/
theorem finite_order : Algebra.FiniteType V (DVRNormalizedFiniteOrder318.Order V d a) := by
  letI : Module.Finite V[X] (DVRNormalizedFiniteOrder318.Order V d a) :=
    (DVRNormalizedFiniteOrder318.finite_free V d a).1
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType V V[X])
    (inferInstance : Algebra.FiniteType V[X] (DVRNormalizedFiniteOrder318.Order V d a))

/-- Same result for the literal reciprocal polynomial order, without
inverting the reciprocal coordinate, twists or discriminant. -/
theorem infinity_order : Algebra.FiniteType V (DVRNormalizedInfinityOrder318.Order V d a) := by
  letI : Module.Finite V[X] (DVRNormalizedInfinityOrder318.Order V d a) :=
    (DVRNormalizedInfinityOrder318.finite_free V d a).1
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType V V[X])
    (inferInstance : Algebra.FiniteType V[X] (DVRNormalizedInfinityOrder318.Order V d a))

variable {A : Type u} [CommRing A] [Algebra V A] [Algebra V[X] A]
  [IsScalarTower V V[X] A]

/-- The ALREADY CONSTRUCTED integral chart point fixes V, by its actual
polynomial evaluation identity. Its underlying ring hom is unchanged. -/
@[expose] def pointAlgHom (T : V) (f : A →+* V)
    (hf : ∀ p : V[X], f (algebraMap V[X] A p)=Polynomial.eval T p) : A →ₐ[V] V where
  __ := f
  commutes' r := by
    change f (algebraMap V A r)=r
    exact congrArg (fun g : V →+* V => g r)
      (NormalizedValuativeChartStructure318.scalar_identity V T f hf)

@[simp] theorem pointAlgHom_toRingHom (T : V) (f : A →+* V)
    (hf : ∀ p : V[X], f (algebraMap V[X] A p)=Polynomial.eval T p) :
    (pointAlgHom V T f hf).toRingHom=f := rfl
end NormalizedChartFiniteType318
