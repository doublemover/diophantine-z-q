module
public import ActualPrimitiveOrderGeneration318
public import ActualPrincipalOpenRestriction318
public section
noncomputable section
namespace ActualPrimitiveRestriction318
open Polynomial ActualPrincipalOpenRestriction318
variable (C R A : Type*) [CommRing C] [CommRing R] [CommRing A]
  [Algebra C R] [Algebra C A] [Algebra.FiniteType C A]
variable (f : R →ₐ[C] A) (d q : R)
/-- Restrict a whole-order generator along one more BASE denominator.
The actual source and base restriction maps commute on every coefficient;
full original generators therefore still generate the entire new order. -/
theorem polynomial_surjective
    (β : Localization.Away (f d))
    (hs : Function.Surjective
      (Polynomial.eval₂RingHom (Localization.awayMap f.toRingHom d) β)) :
    Function.Surjective
      (Polynomial.eval₂RingHom (Localization.awayMap f.toRingHom (d*q))
        (restriction (f d) (f (d*q)) (map_dvd f.toRingHom (dvd_mul_right d q)) β)) := by
  classical
  obtain ⟨s, hsgen⟩ := Algebra.FiniteType.out (R := C) (A := A)
  let rA := restriction (f d) (f (d*q)) (map_dvd f.toRingHom (dvd_mul_right d q))
  let rB := restriction d (d*q) (dvd_mul_right d q)
  let g := Localization.awayMap f.toRingHom d
  let G := Localization.awayMap f.toRingHom (d*q)
  apply ActualPrimitiveOrderGeneration318.polynomial_surjective C R A f (d*q) s hsgen
  intro a _
  obtain ⟨P,hP⟩ := hs (algebraMap A (Localization.Away (f d)) a)
  refine ⟨P.map rB, ?_⟩
  have he := congrArg rA hP
  change rA (Polynomial.eval₂ g β P) = _ at he
  rw [Polynomial.hom_eval₂, restriction_source] at he
  rw [Polynomial.eval₂_map]
  have hsq : rA.comp g = G.comp rB := square f.toRingHom d (d*q) (dvd_mul_right d q)
  rw [hsq] at he
  exact he
end ActualPrimitiveRestriction318
