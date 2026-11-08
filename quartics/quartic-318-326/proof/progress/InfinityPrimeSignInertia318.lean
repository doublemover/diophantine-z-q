module
public import InfinitySignResidue318
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public section
noncomputable section
namespace InfinityPrimeSignInertia318
open Polynomial InfinityReciprocalAction318 InfinityOrderCoordinates318 InfinitySignCoordinates318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
/-- The original reciprocal base coordinate s=1/t in the full infinity order. -/
@[expose] def reciprocalCoordinate:Order c:=
  algebraMap (Base c) (Order c) (algebraMap ℚ[X] (Base c) X)
theorem reciprocal_square:reciprocalCoordinate c=
    algebraMap ℚ (Order c) (↑((c 0)⁻¹):ℚ)*(coordinate c)^2:=
  InfinityOverlapLocalization318.reciprocal_coordinate c

variable {F:Type*} [Field F] [Algebra ℚ F] (p:Order c→+*F)
/-- A field-valued point over the original s=0 base has u=0. Only residue
points are used; the nonreduced s=0 scheme fiber is not replaced by u=0. -/
theorem coordinate_zero_of_reciprocal_zero (hs:p (reciprocalCoordinate c)=0):
    p (coordinate c)=0:=by
  rw [reciprocal_square,map_mul,map_pow] at hs
  have hc:p (algebraMap ℚ (Order c) (↑((c 0)⁻¹):ℚ))≠0:=
    ((((c 0)⁻¹).isUnit.map (algebraMap ℚ (Order c))).map p).ne_zero
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hs).resolve_left hc)

theorem residue_fixed_exactly (hs:p (reciprocalCoordinate c)=0) (b:Fin 4→Bool):
    p.comp (sign c b).toRingHom=p↔b=(fun _=>false)∨b=(fun _=>true):=
  InfinitySignResidue318.fixed_exactly c p (coordinate_zero_of_reciprocal_zero c p hs) b

section Prime
variable (Q:Ideal (Order c)) [Q.IsPrime]
local instance residueRat:Algebra ℚ Q.ResidueField:=
  ((algebraMap (Order c) Q.ResidueField).comp (algebraMap ℚ (Order c))).toAlgebra
variable (hs:reciprocalCoordinate c∈Q)
include hs
/-- Every actual prime on the whole reciprocal chart above s=0 is covered
canonically, with no chosen field presentation. -/
theorem sign_mem_exactly (b:Fin 4→Bool):
    sign c b∈Q.inertia (Order c≃ₐ[Base c]Order c)↔
      b=(fun _=>false)∨b=(fun _=>true):=by
  have hp:algebraMap (Order c) Q.ResidueField (reciprocalCoordinate c)=0:=
    Ideal.algebraMap_residueField_eq_zero.mpr hs
  have h:=InfinitySignResidue318.sign_mem_inertia c (algebraMap (Order c) Q.ResidueField)
    (coordinate_zero_of_reciprocal_zero c (algebraMap (Order c) Q.ResidueField) hp) b
  rw [Ideal.ker_algebraMap_residueField] at h
  exact h

theorem diagonal_quotient_fixed (x:Order c):
    Ideal.Quotient.mk Q (sign c (fun _=>true) x)=Ideal.Quotient.mk Q x:=by
  apply Ideal.Quotient.eq.mpr
  exact (Ideal.mem_inertia.mp ((sign_mem_exactly c Q hs _).mpr (Or.inr rfl))) x
end Prime
end InfinityPrimeSignInertia318
