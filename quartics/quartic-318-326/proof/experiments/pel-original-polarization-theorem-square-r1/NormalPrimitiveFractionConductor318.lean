module
public import FiniteNormalPrimitiveConductor318
public section
noncomputable section
namespace NormalPrimitiveFractionConductor318
open Polynomial
variable (R K A L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Algebra R A] [IsTorsionFree R A] [Module.Finite R A]
  [Field L] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L]

/-- The SAME derivative conductor controls every integral element of
the actual fraction field, not only elements already in the whole chart.
This stronger range statement is what is needed to prove normality. -/
theorem conductor (t : A)
    (hprimitive : Function.Surjective
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L))
    (y : L) (hy : IsIntegral A y) :
    ∃ a : A, algebraMap A L (Polynomial.aeval t (minpoly R t).derivative) * y =
      algebraMap A L a := by
  have ht : IsIntegral R t := IsIntegral.of_finite R t
  have hker : RingHom.ker
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L).toRingHom =
      Ideal.span {(minpoly R t).map (algebraMap R K)} := by
    rw [←minpoly.isIntegrallyClosed_eq_field_fractions K L ht]
    exact minpoly.ker_aeval_eq_span_minpoly K (algebraMap A L t)
  letI : Algebra.IsIntegral R A := ⟨fun a => IsIntegral.of_finite R a⟩
  have hyR : IsIntegral R y := isIntegral_trans (R := R) A hy
  have hsurj : Function.Surjective
      (Polynomial.aeval (algebraMap L L (algebraMap A L t)) : Polynomial K →ₐ[K] L) := by
    simpa only [algebraMap_self, RingHom.id_apply] using hprimitive
  have hk : RingHom.ker
      (Polynomial.aeval (algebraMap L L (algebraMap A L t)) : Polynomial K →ₐ[K] L).toRingHom =
      Ideal.span {(minpoly R t).map (algebraMap R K)} := by
    simpa only [algebraMap_self, RingHom.id_apply] using hker
  obtain ⟨p,hp⟩ := NormalPrimitiveDerivativeConductor318.conductor
    (R := R) (K := K) (A := L) (L := L) (algebraMap A L t) (minpoly R t)
    (minpoly.monic ht) hsurj hk y hyR
  have heval (q : Polynomial R) :
      Polynomial.aeval (algebraMap A L t) q = algebraMap A L (Polynomial.aeval t q) := by
    simpa only [Polynomial.map_id] using (Polynomial.map_aeval_eq_aeval_map
      (φ := RingHom.id R) (ψ := algebraMap A L)
      (by rw [RingHom.comp_id,←IsScalarTower.algebraMap_eq R A L]) q t).symm
  refine ⟨Polynomial.aeval t p,?_⟩
  simpa only [heval] using hp
end NormalPrimitiveFractionConductor318
