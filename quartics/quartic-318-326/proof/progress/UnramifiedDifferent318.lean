module
public import LocalDivisorData318
public section
noncomputable section
namespace UnramifiedDifferent318
open Module Algebra IsDiscreteValuationRing IsLocalRing Submodule.IsPrincipal
open LenstraVertical318 LocalDivisorData318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Actual unramifiedness at the closed point makes the actual different
ideal the unit ideal; no zero coefficient is assumed. -/
theorem different_eq_top (A B:Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (hu:Algebra.IsUnramifiedAt A (maximalIdeal B)) : differentIdeal A B=⊤ := by
  have hn:¬maximalIdeal B∣differentIdeal A B := not_dvd_differentIdeal_iff.mpr hu
  by_contra h
  exact hn (Ideal.dvd_iff_le.mpr (le_maximalIdeal h))

/-- Hence its actual normalized different exponent is zero. -/
theorem different_exponent_zero (A B:Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (hu:Algebra.IsUnramifiedAt A (maximalIdeal B)) : differentExponent A B=0 := by
  have hs:Ideal.span {generator (differentIdeal A B)}=⊤ :=
    (Ideal.span_singleton_generator _).trans (different_eq_top A B hu)
  have hg:IsUnit (generator (differentIdeal A B)) := Ideal.span_singleton_eq_top.mp hs
  simp only [differentExponent,addVal_eq_zero_iff.mpr hg,ENat.toNat_zero]

/-- A geometric local-ring certificate for an unramified component. The
canonical coefficient is identified with the actual different, not with zero. -/
structure Data (canonical pullback:ℝ) where
  extension : LocalExtension
  finite_integral : Module.Finite extension.A extension.B
  unramified : Algebra.IsUnramifiedAt extension.A (maximalIdeal extension.B)
  canonical_eq : canonical=(extension.different:ℝ)
  pullback_nonneg : 0≤pullback

/-- The zero coefficient is a consequence of the actual unramified algebra. -/
theorem Data.canonical_zero {canonical pullback:ℝ} (D:Data canonical pullback) :
    canonical=0 := by
  let E:=D.extension
  letI:Module.Finite E.A E.B:=D.finite_integral
  have h:E.different=0 := different_exponent_zero E.A E.B D.unramified
  exact D.canonical_eq.trans (by rw [h,Nat.cast_zero])

/-- Construct the frozen local coefficient input from actual unramifiedness. -/
@[expose] def Data.toCoefficientData {d:ℕ} {canonical pullback:ℝ}
    (D:Data canonical pullback) : CoefficientData d canonical pullback :=
  .unramified D.canonical_zero D.pullback_nonneg

end UnramifiedDifferent318
