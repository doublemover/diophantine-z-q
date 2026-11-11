module
public import FourRootDerivativeZeroFinite318
public import FiniteReducedComplexAlgebra318
public section
noncomputable section
namespace FourRootDerivativeZeroSections318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
/-- H0 is the existing structure sheaf's genuine global section ring. -/
abbrev H0 := Γ(zeroScheme b, ⊤)
/-- The scalar map is the actual structural pullback, with the canonical
Spec(C) global-section identification, not a chosen abstract field action. -/
@[expose] def baseHom : ℂ →+* H0 b :=
  (FourRootDerivativeZeroFinite318.structure b).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
instance algebra : Algebra ℂ (H0 b) := (baseHom b).toAlgebra
/-- The same structural map is finite; hence its actual pullback on
all global sections is finite over the canonical complex scalars. -/
theorem finite : Module.Finite ℂ (H0 b) := by
  letI := FourRootDerivativeZeroFinite318.finite b hb
  apply RingHom.finite_algebraMap.mp
  change (baseHom b).Finite
  exact (FourRootDerivativeZeroFinite318.structure b).finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
theorem reduced : _root_.IsReduced (H0 b) := by
  letI := FourRootDerivativeZeroReduced318.reduced b hb
  infer_instance
/-- The original global-section algebra is etale, with no change to
its canonical structural scalar map. -/
theorem etale : Algebra.Etale ℂ (H0 b) := by
  letI := finite b hb
  letI := reduced b hb
  exact FiniteReducedComplexAlgebra318.etale (H0 b)
/-- Actual global sections split as one complex factor at every prime.
Counting those primes and identifying cotangent H0 are separate steps. -/
@[expose] def split : H0 b ≃ₐ[ℂ] (PrimeSpectrum (H0 b) → ℂ) := by
  letI := finite b hb
  letI := reduced b hb
  exact FiniteReducedComplexAlgebra318.split (H0 b)
end FourRootDerivativeZeroSections318
