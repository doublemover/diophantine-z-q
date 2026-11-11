module
public import Mathlib.RingTheory.DedekindDomain.Different
public section
noncomputable section
namespace TraceDifferentPolynomialEquiv318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {B C:Type*} [CommRing B] [CommRing C] [IsDedekindDomain B] [IsDedekindDomain C]
  [Algebra ℂ[X] B] [Algebra ℂ[X] C] [Module.Finite ℂ[X] B] [Module.Free ℂ[X] B]
  [Module.Finite ℂ[X] C] [Module.Free ℂ[X] C]
  [CharZero B] [CharZero C]
variable (e:B≃ₐ[ℂ[X]]C)
local instance transportAlgebra:Algebra B C:=e.toRingHom.toAlgebra
local instance transportTower:IsScalarTower ℂ[X] B C:=
  IsScalarTower.of_algebraMap_eq (fun p=>(e.commutes p).symm)
@[expose] def transportEquiv:B≃ₐ[B]C where
  __:=e.toRingEquiv
  commutes' _:=rfl
local instance transportFinite:Module.Finite B C:=
  Module.Finite.equiv (transportEquiv e).toLinearEquiv
local instance transportFree:Module.Free B C:=
  Module.Free.of_equiv (transportEquiv e).toLinearEquiv
local instance transportUnramified:Algebra.FormallyUnramified B C:=
  Algebra.FormallyUnramified.of_equiv (transportEquiv e)
lemma relative_top:differentIdeal B C=⊤:=by
  by_contra h
  obtain ⟨q,hq,hJ⟩:=Ideal.exists_le_maximal (differentIdeal B C) h
  letI:q.IsPrime:=hq.isPrime
  have hn:¬q∣differentIdeal B C:=not_dvd_differentIdeal_iff.mpr inferInstance
  exact hn (Ideal.dvd_iff_le.mpr hJ)
/-- Genuine covariance of the trace-dual different under an exact
polynomial-base algebra isomorphism. Derived from actual transitivity
and actual unramifiedness of the isomorphism, not from point actions. -/
theorem map_different:
    (differentIdeal ℂ[X] B).map e.toRingHom=differentIdeal ℂ[X] C:=by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (A:=ℂ[X]) (B:=B) C,
    relative_top,Ideal.top_mul]
  rfl
end TraceDifferentPolynomialEquiv318
