module
public import IntegralWholeFiniteComparison318
public section
noncomputable section
namespace IntegralWholeReciprocalLocalization318
open Polynomial IntegralWholeReciprocalOverlap318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem u_unit : IsUnit (u R c) :=
  ((c 0).isUnit.map (algebraMap R (Laurent R))).mul ((y R)⁻¹).isUnit

@[expose] def inversion : Laurent R →ₐ[R] Laurent R :=
  IsLocalization.Away.liftAlgHom (f:=reciprocalMap R c) (X:R[X])
    (by simpa only [reciprocalMap,Polynomial.aeval_X] using u_unit R c)

theorem inversion_polynomial (p : R[X]) :
    inversion R c (algebraMap R[X] (Laurent R) p)=reciprocalMap R c p :=
  IsLocalization.Away.lift_eq ..

theorem inversion_y : inversion R c (y R:Laurent R)=u R c := by
  rw [y_value,inversion_polynomial]
  exact Polynomial.aeval_X _

theorem inversion_u : inversion R c (u R c)=(y R:Laurent R) := by
  have h := congrArg (inversion R c) (yu R c)
  rw [map_mul,inversion_y,AlgHom.commutes] at h
  apply (u_unit R c).mul_left_cancel.mp
  exact h.trans ((mul_comm _ _).trans (yu R c)).symm

theorem inversion_twice_polynomial (p : R[X]) :
    inversion R c (reciprocalMap R c p)=algebraMap R[X] (Laurent R) p := by
  have h : (inversion R c).comp (reciprocalMap R c)=
      IsScalarTower.toAlgHom R R[X] (Laurent R) := by
    apply Polynomial.algHom_ext
    change inversion R c (Polynomial.aeval (u R c) X)=algebraMap R[X] (Laurent R) X
    rw [Polynomial.aeval_X,inversion_u,y_value]
  exact AlgHom.congr_fun h p

theorem inversion_twice (z : Laurent R) : inversion R c (inversion R c z)=z := by
  have h : (inversion R c).toRingHom.comp (inversion R c).toRingHom=RingHom.id (Laurent R) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X:R[X]))
    apply RingHom.ext
    intro p
    change inversion R c (inversion R c (algebraMap R[X] (Laurent R) p))=_
    rw [inversion_polynomial,inversion_twice_polynomial]
    rfl
  exact RingHom.congr_fun h z

/-- The native fraction witnesses are fixed before introducing the different
reciprocal polynomial scalar action on the same Laurent carrier. -/
theorem native_fraction (z : Laurent R) :
    ∃ n : ℕ,∃ p : R[X],z*(y R:Laurent R)^n=algebraMap R[X] (Laurent R) p := by
  simpa only [y_value] using IsLocalization.Away.surj (X:R[X]) z

theorem native_eq {a b : R[X]}
    (h : algebraMap R[X] (Laurent R) a=algebraMap R[X] (Laurent R) b) :
    ∃ n : ℕ,(X:R[X])^n*a=X^n*b :=
  IsLocalization.Away.exists_of_eq (X:R[X]) h

section ReciprocalScalar

/-- Under the literal reciprocal substitution, this SAME Laurent ring is
also the full X localization. This proves the full reciprocal source open,
not only the smaller open where its root factors are invertible. -/
theorem reciprocal_localization :
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R c).toRingHom.toAlgebra
  IsLocalization.Away (X:R[X]) (Laurent R) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R c).toRingHom.toAlgebra
  apply IsLocalization.Away.mk (X:R[X])
  · change IsUnit (reciprocalMap R c X)
    simpa only [reciprocalMap,Polynomial.aeval_X] using u_unit R c
  · intro z
    obtain ⟨n,p,hp⟩ := native_fraction R (inversion R c z)
    refine ⟨n,p,?_⟩
    have h := congrArg (inversion R c) hp
    rw [map_mul,map_pow,inversion_twice,inversion_y,inversion_polynomial] at h
    simpa only [reciprocalMap,Polynomial.aeval_X] using h
  · intro a b hab
    have h := congrArg (inversion R c) hab
    change inversion R c (reciprocalMap R c a)=inversion R c (reciprocalMap R c b) at h
    rw [inversion_twice_polynomial,inversion_twice_polynomial] at h
    exact native_eq R h
end ReciprocalScalar
end IntegralWholeReciprocalLocalization318
