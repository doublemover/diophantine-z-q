module
public import IntegralInfinityOverlapRealization318
public import FourRootUnitScale318
public section
noncomputable section
namespace NormalizedReciprocalLaurent318
open Polynomial
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R]
abbrev Laurent := Localization.Away (X:R[X])
@[expose] def coordinate : (Laurent R)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S:=Laurent R) (X:R[X])).unit
@[simp] theorem coordinate_value : (coordinate R:Laurent R)=algebraMap R[X] (Laurent R) X :=
  IsUnit.unit_spec _
@[expose] def reciprocalMap : R[X] →ₐ[R] Laurent R :=
  Polynomial.aeval (↑(coordinate R)⁻¹:Laurent R)

theorem reciprocal_unit : IsUnit (reciprocalMap R X) := by
  simpa only [reciprocalMap,Polynomial.aeval_X] using ((coordinate R)⁻¹).isUnit
@[expose] def inversion : Laurent R →ₐ[R] Laurent R :=
  IsLocalization.Away.liftAlgHom (f:=reciprocalMap R) (X:R[X]) (reciprocal_unit R)

theorem inversion_polynomial (p : R[X]) :
    inversion R (algebraMap R[X] (Laurent R) p)=reciprocalMap R p :=
  IsLocalization.Away.lift_eq _ (reciprocal_unit R) p

theorem inversion_coordinate : inversion R (coordinate R:Laurent R)=(↑(coordinate R)⁻¹:Laurent R) := by
  rw [coordinate_value,inversion_polynomial]
  exact Polynomial.aeval_X _

theorem inversion_inverse : inversion R (↑(coordinate R)⁻¹:Laurent R)=(coordinate R:Laurent R) := by
  have h := IntegralInfinityBaseEquiv318.map_unit_inverse (inversion R).toRingHom
    (coordinate R) (coordinate R)⁻¹ (inversion_coordinate R)
  simpa only [inv_inv] using h

theorem inversion_twice_polynomial (p : R[X]) :
    inversion R (reciprocalMap R p)=algebraMap R[X] (Laurent R) p := by
  have h : (inversion R).comp (reciprocalMap R)=IsScalarTower.toAlgHom R R[X] (Laurent R) := by
    apply Polynomial.algHom_ext
    change inversion R (Polynomial.aeval (↑(coordinate R)⁻¹:Laurent R) X)=algebraMap R[X] (Laurent R) X
    rw [Polynomial.aeval_X,inversion_inverse,coordinate_value]
  exact AlgHom.congr_fun h p

theorem inversion_twice (z : Laurent R) : inversion R (inversion R z)=z := by
  have h : (inversion R).toRingHom.comp (inversion R).toRingHom=RingHom.id (Laurent R) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X:R[X]))
    apply RingHom.ext
    intro p
    change inversion R (inversion R (algebraMap R[X] (Laurent R) p))=_
    rw [inversion_polynomial,inversion_twice_polynomial]
  exact RingHom.congr_fun h z

theorem native_fraction (z : Laurent R) :
    ∃ n : ℕ,∃ p : R[X],z*(coordinate R:Laurent R)^n=algebraMap R[X] (Laurent R) p := by
  simpa only [coordinate_value] using IsLocalization.Away.surj (X:R[X]) z

theorem native_eq {a b : R[X]}
    (h : algebraMap R[X] (Laurent R) a=algebraMap R[X] (Laurent R) b) :
    ∃ n : ℕ,(X:R[X])^n*a=X^n*b := IsLocalization.Away.exists_of_eq (X:R[X]) h

section Reciprocal
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
/-- The same Laurent carrier is the full principal localization also under
its actual reciprocal scalar action; no branch factors are inverted. -/
theorem reciprocal_localization : IsLocalization.Away (X:R[X]) (Laurent R) := by
  apply IsLocalization.Away.mk (X:R[X])
  · exact reciprocal_unit R
  · intro z
    obtain ⟨n,p,hp⟩ := native_fraction R (inversion R z)
    refine ⟨n,p,?_⟩
    have h := congrArg (inversion R) hp
    rw [map_mul,map_pow,inversion_twice,inversion_coordinate,inversion_polynomial] at h
    simpa only [reciprocalMap,Polynomial.aeval_X] using h
  · intro a b hab
    have h := congrArg (inversion R) hab
    change inversion R (reciprocalMap R a)=inversion R (reciprocalMap R b) at h
    rw [inversion_twice_polynomial,inversion_twice_polynomial] at h
    exact native_eq R h
end Reciprocal
end NormalizedReciprocalLaurent318
