module
public import FiniteNormalBaseMonogenicSuborder318
public import NormalPrimitiveDerivativeConductor318
public import ConductorLocalizationEquivalence318
public section
noncomputable section
namespace FiniteNormalPrimitiveConductor318
open Polynomial FiniteNormalBaseMonogenicSuborder318
variable (R K A L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Algebra R A] [IsTorsionFree R A] [Module.Finite R A]
  [Field L] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L]

/-- Literal polynomial elements of the monogenic order retain their
actual evaluation in the whole original finite algebra. -/
lemma embedding_mk (t : A) (p : Polynomial R) :
    embedding R A t (AdjoinRoot.mk (minpoly R t) p) = Polynomial.aeval t p := by
  have h : (embedding R A t).comp
      (Polynomial.aeval (AdjoinRoot.root (minpoly R t))) = Polynomial.aeval t := by
    ext
    simp only [AlgHom.comp_apply,Polynomial.aeval_X,embedding_root]
  have hp := congrArg (fun f : Polynomial R →ₐ[R] A => f p) h
  simpa only [AlgHom.comp_apply,AdjoinRoot.aeval_eq] using hp

/-- The derivative of the ACTUAL minimal polynomial is a conductor of
the full finite algebra. Primitive generation is required in its exact
fraction field, not guessed from separation of one finite point fiber. -/
theorem derivative_conductor (t : A)
    (hprimitive : Function.Surjective
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L)) :
    ∀ a : A, ∃ b : AdjoinRoot (minpoly R t),
      embedding R A t (AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative) * a =
        embedding R A t b := by
  intro a
  have ht : IsIntegral R t := IsIntegral.of_finite R t
  have hker : RingHom.ker
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L).toRingHom =
      Ideal.span {(minpoly R t).map (algebraMap R K)} := by
    rw [←minpoly.isIntegrallyClosed_eq_field_fractions K L ht]
    exact minpoly.ker_aeval_eq_span_minpoly K (algebraMap A L t)
  obtain ⟨p,hp⟩ := NormalPrimitiveDerivativeConductor318.conductor
    (K := K) (L := L) t (minpoly R t) (minpoly.monic ht) hprimitive hker a
    (IsIntegral.of_finite R a)
  refine ⟨AdjoinRoot.mk (minpoly R t) p,?_⟩
  simpa only [embedding_mk] using hp

/-- Inverting precisely the derivative identifies the whole finite
algebra with the actual monogenic order on that same principal open. -/
@[expose] def derivativeOpenEquiv (t : A)
    (hprimitive : Function.Surjective
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L)) :
    Localization.Away (AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative) ≃+*
      Localization.Away (embedding R A t
        (AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative)) :=
  ConductorLocalizationEquivalence318.equivalence (embedding R A t).toRingHom
    (embedding_injective R A t) _ (derivative_conductor R K A L t hprimitive)
end FiniteNormalPrimitiveConductor318
