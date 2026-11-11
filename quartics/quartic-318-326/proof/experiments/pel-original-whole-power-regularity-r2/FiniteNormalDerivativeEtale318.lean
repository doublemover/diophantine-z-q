module
public import FiniteNormalPrimitiveConductor318
public import Mathlib.RingTheory.Etale.StandardEtale
public section
noncomputable section
namespace FiniteNormalDerivativeEtale318
open Polynomial FiniteNormalBaseMonogenicSuborder318

/-- Every monic equation is standard etale on its exact derivative
open. No global separability or extra base denominator is needed. -/
theorem quotient_etale {R : Type*} [CommRing R] (Q : Polynomial R) (hm : Q.Monic) :
    Algebra.Etale R (Localization.Away (AdjoinRoot.mk Q Q.derivative)) := by
  let P : StandardEtalePair R :=
    { f := Q
      monic_f := hm
      g := Q.derivative
      cond := ⟨1,0,1,by simp⟩ }
  exact Algebra.Etale.of_equiv P.equivAwayAdjoinRoot

variable (R K A L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Algebra R A] [IsTorsionFree R A] [Module.Finite R A]
  [Field L] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L]

/-- The WHOLE finite algebra, localized only at the actual derivative
of its primitive integral element, is etale over the ORIGINAL normal
base. The base scalar structure is inherited through the original A. -/
theorem whole_derivative_open_etale (t : A)
    (hprimitive : Function.Surjective
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L)) :
    Algebra.Etale R (Localization.Away (embedding R A t
      (AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative))) := by
  let c := AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative
  letI : Algebra.Etale R (Localization.Away c) :=
    quotient_etale (minpoly R t) (minpoly.monic (IsIntegral.of_finite R t))
  let e : Localization.Away c ≃ₐ[R] Localization.Away (embedding R A t c) :=
    ConductorLocalizationEquivalence318.algEquivalence (embedding R A t)
      (embedding_injective R A t) c
      (FiniteNormalPrimitiveConductor318.derivative_conductor R K A L t hprimitive)
  exact Algebra.Etale.of_equiv e
end FiniteNormalDerivativeEtale318
