module
public import IntegralWholeReciprocalOrders318
public section
noncomputable section
namespace IntegralWholeReciprocalOverlap318
open Polynomial IntegralWholeReciprocalOrders318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
abbrev Laurent := Localization.Away (X:R[X])
@[expose] def y : (Laurent R)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S:=Laurent R) (X:R[X])).unit
@[expose] def u : Laurent R := algebraMap R (Laurent R) (c 0:R) * (↑(y R)⁻¹:Laurent R)
@[expose] def reciprocalMap : R[X] →ₐ[R] Laurent R := Polynomial.aeval (u R c)
@[expose] def finiteParameter (j : Fin 3) : Laurent R :=
  algebraMap R[X] (Laurent R) (finiteCoefficient R c j)
@[expose] def infinityParameter (j : Fin 3) : Laurent R :=
  reciprocalMap R c (IntegralInfinityChart318.coefficient R c j)

@[simp] theorem y_value : (y R:Laurent R)=algebraMap R[X] (Laurent R) X :=
  IsUnit.unit_spec _

theorem yu : (y R:Laurent R)*u R c=algebraMap R (Laurent R) (c 0:R) := by
  rw [u]
  calc
    _ = algebraMap R (Laurent R) (c 0:R)*((y R:Laurent R)*(↑(y R)⁻¹:Laurent R)) := by ring
    _ = _ := by rw [Units.mul_inv,mul_one]

/-- The full radicands match with their literal y0² factor. This identity
requires only the original twist unit, not nonzero other-root factors. -/
theorem parameter_identity (j : Fin 3) :
    finiteParameter R c j=infinityParameter R c j*(y R:Laurent R)^2 := by
  have hk : algebraMap R (Laurent R) (c 0:R)*
      algebraMap R (Laurent R) (↑(c 0)⁻¹:R)=1 := by
    rw [←map_mul,Units.mul_inv,map_one]
  have h := IntegralReciprocalRootScale318.parameter_identity
    (algebraMap R (Laurent R) (c 0:R))
    (algebraMap R (Laurent R) (↑(c 0)⁻¹:R))
    (y R:Laurent R) (u R c)
    (algebraMap R (Laurent R) (IntegralInfinityChart318.contact R j))
    (algebraMap R (Laurent R) (c j.succ:R)) hk (yu R c)
  have hf : finiteParameter R c j=
      algebraMap R (Laurent R) (c j.succ:R)*
      (algebraMap R (Laurent R) (↑(c 0)⁻¹:R)*(y R:Laurent R)^2-
        algebraMap R (Laurent R) (IntegralInfinityChart318.contact R j)) := by
    simp only [finiteParameter,finiteCoefficient,map_mul,map_sub,map_pow,y_value]
    rfl
  have hi : infinityParameter R c j=
      algebraMap R (Laurent R) (c j.succ:R)*
      algebraMap R (Laurent R) (↑(c 0)⁻¹:R)*
      (1-algebraMap R (Laurent R) (IntegralInfinityChart318.contact R j)*
        algebraMap R (Laurent R) (↑(c 0)⁻¹:R)*(u R c)^2) := by
    simp only [infinityParameter,reciprocalMap,IntegralInfinityChart318.coefficient,
      map_mul,map_sub,map_one,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]
  rw [hf,hi]
  exact h.symm.trans (mul_comm _ _)

/-- The entire punctured orders are isomorphic, including zero radicands.
Unlike the earlier etale overlap, no product of branch factors is inverted. -/
@[expose] def fullOverlap :
    ThreeRootOrder318.Order (finiteParameter R c) ≃ₐ[Laurent R]
      ThreeRootOrder318.Order (infinityParameter R c) :=
  UnitScaledQuadraticOrder318.three _ _ (y R) (parameter_identity R c)

/-- The finite side really is base change of the full finite polynomial
order along the canonical principal localization. -/
@[expose] def finiteBaseChange :
    Laurent R ⊗[R[X]] FiniteOrder R c ≃ₐ[Laurent R]
      ThreeRootOrder318.Order (finiteParameter R c) :=
  ThreeRootOrder318.baseChange _ _

section ReciprocalScalar
/-- On the reciprocal side the scalar action is the actual substitution
u=c0/y0, not the canonical polynomial localization action. -/
@[expose] def infinityBaseChange :
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R c).toRingHom.toAlgebra
  Laurent R ⊗[R[X]] InfinityOrder R c ≃ₐ[Laurent R]
      ThreeRootOrder318.Order (infinityParameter R c) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R c).toRingHom.toAlgebra
  exact ThreeRootOrder318.baseChange (R:=Polynomial R)
    (IntegralInfinityChart318.coefficient R c) (Laurent R)
end ReciprocalScalar
end IntegralWholeReciprocalOverlap318
