module
public import IntegralReciprocalBase318
public import LocalizedNormalModel318
public import Mathlib.RingTheory.RingHom.Etale
public section
noncomputable section
namespace IntegralReciprocalNormalClosures318
open Polynomial IntegralReciprocalBase318
set_option maxHeartbeats 1000000
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a : Fin 4 → R) (N : R)
  (B : Type u) [CommRing B] [IsDomain B] [Algebra (FiniteBase R a N) B]
  [Module.Finite (FiniteBase R a N) B] [Algebra.Etale (FiniteBase R a N) B]

@[expose] def reciprocalCoverHom : ReciprocalBase R a N →+* B :=
  (algebraMap (FiniteBase R a N) B).comp (backward R a N)
theorem reciprocal_finite : (reciprocalCoverHom R a N B).Finite :=
  (RingHom.finite_algebraMap.mpr inferInstance).comp (reciprocalEquiv R a N).symm.finite
theorem reciprocal_etale : (reciprocalCoverHom R a N B).Etale :=
  RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (reciprocalEquiv R a N).symm.bijective)
    (RingHom.etale_algebraMap.mpr inferInstance)
@[expose] def reciprocalPolynomialMap : R[X] →+* B :=
  (reciprocalCoverHom R a N B).comp (algebraMap R[X] (ReciprocalBase R a N))
@[expose] def finitePolynomialMap : R[X] →+* B :=
  (algebraMap (FiniteBase R a N) B).comp (algebraMap R[X] (FiniteBase R a N))

/-- The genuine reciprocal integral closure is finite, normal and Noetherian
for its literal scalar map s ↦ t⁻¹. No finiteness of normalization is assumed. -/
theorem reciprocal_normal_closure (hN : N ≠ 0) :
    letI := (reciprocalPolynomialMap R a N B).toAlgebra
    Module.Finite R[X] (integralClosure R[X] B) ∧
    IsIntegrallyClosed (integralClosure R[X] B) ∧
    IsNoetherianRing (integralClosure R[X] B) := by
  letI := (reciprocalPolynomialMap R a N B).toAlgebra
  letI := (reciprocalCoverHom R a N B).toAlgebra
  letI : IsScalarTower R[X] (ReciprocalBase R a N) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module.Finite (ReciprocalBase R a N) B := reciprocal_finite R a N B
  letI : Algebra.Etale (ReciprocalBase R a N) B := reciprocal_etale R a N B
  have hd := reciprocalDenominator_ne_zero R a N hN
  have h := LocalizedNormalModel318.finite_normal_model (Rf := ReciprocalBase R a N)
    (B := B) (reciprocalDenominator R a N) hd
  exact ⟨h.1,h.2,LocalizedNormalModel318.model_noetherian (Rf := ReciprocalBase R a N)
    (B := B) (reciprocalDenominator R a N) hd⟩

/-- The finite-coordinate closure uses the same whole source B, with its
original scalar action rather than the reciprocal action. -/
theorem finite_normal_closure (hN : N ≠ 0) :
    letI := (finitePolynomialMap R a N B).toAlgebra
    Module.Finite R[X] (integralClosure R[X] B) ∧
    IsIntegrallyClosed (integralClosure R[X] B) ∧
    IsNoetherianRing (integralClosure R[X] B) := by
  letI := (finitePolynomialMap R a N B).toAlgebra
  letI : IsScalarTower R[X] (FiniteBase R a N) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hd := finiteDenominator_ne_zero R a N hN
  have h := LocalizedNormalModel318.finite_normal_model (Rf := FiniteBase R a N)
    (B := B) (finiteDenominator R a N) hd
  exact ⟨h.1,h.2,LocalizedNormalModel318.model_noetherian (Rf := FiniteBase R a N)
    (B := B) (finiteDenominator R a N) hd⟩
end IntegralReciprocalNormalClosures318
