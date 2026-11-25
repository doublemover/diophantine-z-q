module
public import SmoothOpenModel318
public import OpenJModel318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace LocalizedNormalModel318
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R Rf B:Type u} [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R]
  [CommRing Rf] [Algebra R Rf]
  [CommRing B] [IsDomain B] [Algebra R B] [Algebra Rf B]
  [IsScalarTower R Rf B] [Algebra.Smooth Rf B] [Module.Finite Rf B]
  (d:R) [IsLocalization.Away d Rf]

include Rf in
/-- The actual integral closure model of a connected finite smooth denominator
open is both finite and normal. No generic-field, separability, open-normality
or finite-normalization hypothesis is supplied. -/
theorem finite_normal_model (hd:d≠0) :
    Module.Finite R (integralClosure R B) ∧ IsIntegrallyClosed (integralClosure R B) := by
  have hM:Submonoid.powers d≤R⁰:=by
    rintro _ ⟨n,rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd)
  let : IsDomain Rf:=IsLocalization.isDomain_of_le_nonZeroDivisors Rf hM
  let : IsIntegrallyClosed Rf:=isIntegrallyClosed_of_isLocalization Rf (Submonoid.powers d) hM
  let K:=FractionRing R
  have hu:IsUnit (algebraMap R K d):=IsUnit.mk0 _ (by
    simpa using (IsFractionRing.injective R K).ne hd)
  let φ:Rf→+*K:=IsLocalization.Away.lift d hu
  let : Algebra Rf K:=φ.toAlgebra
  let : IsScalarTower R Rf K:=IsScalarTower.of_algebraMap_eq (by
    intro r
    exact (IsLocalization.Away.lift_eq d hu r).symm)
  let : IsFractionRing Rf K:=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) Rf K
  exact ⟨SmoothOpenModel318.model_finite (Rf:=Rf) (K:=K),
    SmoothOpenModel318.model_normal (Rf:=Rf) (K:=K)⟩

include Rf in
/-- Actual finite/proper affine geometry of that normal model. -/
theorem finite_proper_model (hd:d≠0) :
    IsFinite (AffineIntegralModel318.structureMap (R:=R) (B:=B)) ∧
      IsProper (AffineIntegralModel318.structureMap (R:=R) (B:=B)) := by
  let : Module.Finite R (integralClosure R B):=(finite_normal_model (Rf:=Rf) (B:=B) d hd).1
  let : IsFinite (AffineIntegralModel318.structureMap (R:=R) (B:=B)):=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact ⟨inferInstance,inferInstance⟩

include Rf in
/-- The constructed normal model also has an actual Noetherian coordinate ring. -/
theorem model_noetherian (hd:d≠0) : IsNoetherianRing (integralClosure R B) := by
  let : Module.Finite R (integralClosure R B):=(finite_normal_model (Rf:=Rf) (B:=B) d hd).1
  exact isNoetherianRing_iff.mpr (isNoetherian_of_tower R (inferInstance:IsNoetherian R (integralClosure R B)))

end LocalizedNormalModel318

namespace OpenJNormalModel318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0

lemma denominator_ne_zero (N:ℕ) (hN:N≠0) : OpenJModel318.denominator N≠0 := by
  unfold OpenJModel318.denominator
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hN)
    · exact Polynomial.X_ne_zero
  · simpa using Polynomial.X_sub_C_ne_zero (1728:ℤ)

variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Algebra (Polynomial ℤ) B]
  [IsScalarTower (Polynomial ℤ) (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]

/-- Exact source open-j specialization: actual connected finite etale cover
produces a finite normal Noetherian model over the integral affine j-line. -/
theorem actual_finite_normal_model (hN:N≠0) :
    Module.Finite (Polynomial ℤ) (integralClosure (Polynomial ℤ) B) ∧
      IsIntegrallyClosed (integralClosure (Polynomial ℤ) B) ∧
      IsNoetherianRing (integralClosure (Polynomial ℤ) B) := by
  have h:=LocalizedNormalModel318.finite_normal_model
    (Rf:=OpenJModel318.Base N) (B:=B) (OpenJModel318.denominator N) (denominator_ne_zero N hN)
  exact ⟨h.1,h.2,LocalizedNormalModel318.model_noetherian
    (Rf:=OpenJModel318.Base N) (B:=B) (OpenJModel318.denominator N) (denominator_ne_zero N hN)⟩

theorem actual_finite_proper_model (hN:N≠0) :
    IsFinite (AffineIntegralModel318.structureMap (R:=Polynomial ℤ) (B:=B)) ∧
      IsProper (AffineIntegralModel318.structureMap (R:=Polynomial ℤ) (B:=B)) :=
  LocalizedNormalModel318.finite_proper_model (Rf:=OpenJModel318.Base N) (B:=B)
    (OpenJModel318.denominator N) (denominator_ne_zero N hN)

end OpenJNormalModel318
