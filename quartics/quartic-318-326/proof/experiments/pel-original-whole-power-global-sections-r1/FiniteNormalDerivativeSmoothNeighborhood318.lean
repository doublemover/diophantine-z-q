module
public import FiniteNormalDerivativeEtale318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Analysis.Complex.Basic
public section
noncomputable section
namespace FiniteNormalDerivativeSmoothNeighborhood318
open AlgebraicGeometry CategoryTheory Polynomial FiniteNormalBaseMonogenicSuborder318
variable (R K A L : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Algebra R A] [IsTorsionFree R A] [Module.Finite R A]
  [Field L] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L]
  [Algebra ℂ R] [Algebra ℂ A] [IsScalarTower ℂ R A] [Algebra.Smooth ℂ R]

/-- A nonvanishing actual primitive derivative supplies a genuine smooth
scheme neighborhood containing the SPECIFIED complex point. This is the
algebraic consumer for an independently proved pointwise derivative
nonvanishing result; neither that result nor primitivity is assumed
from point separation or equality of analytic images. -/
theorem point_has_smooth_open (t : A)
    (hprimitive : Function.Surjective
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L))
    (v : A →ₐ[ℂ] ℂ)
    (hv : v (Polynomial.aeval t (minpoly R t).derivative) ≠ 0) :
    let c := embedding R A t (AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative)
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away c)))) ∧
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away c)))) ∧
    ∃ u : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away c)),
      u ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away c))) =
        Spec.map (CommRingCat.ofHom v.toRingHom) := by
  let c := embedding R A t (AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative)
  have hc : v c ≠ 0 := by
    simpa only [c,FiniteNormalPrimitiveConductor318.embedding_mk] using hv
  letI : Algebra.Etale R (Localization.Away c) :=
    FiniteNormalDerivativeEtale318.whole_derivative_open_etale R K A L t hprimitive
  letI : Algebra.Smooth ℂ (Localization.Away c) :=
    Algebra.Smooth.comp ℂ R (Localization.Away c)
  let f : Localization.Away c →ₐ[ℂ] ℂ :=
    IsLocalization.Away.liftAlgHom c (f := v) (isUnit_iff_ne_zero.mpr hc)
  refine ⟨IsOpenImmersion.of_isLocalization c,
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance),
    Spec.map (CommRingCat.ofHom f.toRingHom),?_⟩
  rw [←Spec.map_comp]
  congr 1
  ext a
  exact IsLocalization.Away.lift_eq c (isUnit_iff_ne_zero.mpr hc) a
end FiniteNormalDerivativeSmoothNeighborhood318
