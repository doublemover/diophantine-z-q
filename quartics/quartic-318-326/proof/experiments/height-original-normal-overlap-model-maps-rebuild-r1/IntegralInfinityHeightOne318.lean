module
public import IntegralInfinityArithmeticDomain318
public import IntegralArithmeticHeightOne318
public section
noncomputable section
namespace IntegralInfinityHeightOne318
open Polynomial IntegralInfinityChart318 IntegralInfinityArithmeticDomain318
open scoped nonZeroDivisors
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] [IsDomain R] [Algebra R ℚ]
  [IsIntegrallyClosed R] [IsNoetherianRing R] (c : Fin 4 → Rˣ)

theorem base_normal : IsIntegrallyClosed (Base R c) := by
  apply isIntegrallyClosed_of_isLocalization (Base R c) (Submonoid.powers (denominator R c))
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (denominator_ne_zero R c))

theorem base_noetherian : IsNoetherianRing (Base R c) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (denominator R c)) (Base R c) inferInstance

/-- Normality includes the genuine infinity fiber u=0: the entire infinity
order is finite etale over its normal integral coordinate base. -/
theorem order_normal (hR : Function.Injective (algebraMap R ℚ))
    (h2 : IsUnit (2 : R)) : IsIntegrallyClosed (Order R c) := by
  letI := base_domain R c
  letI := base_normal R c
  letI := order_domain R c hR
  letI : Module.Finite (Base R c) (Order R c) := (finite_free_etale R c h2).1
  letI : Algebra.Etale (Base R c) (Order R c) := (finite_free_etale R c h2).2.2
  exact SmoothGenericField318.smooth_integrallyClosed
    (R := Base R c) (K := FractionRing (Base R c)) (B := Order R c)

theorem order_noetherian : IsNoetherianRing (Order R c) := by
  letI := base_noetherian R c
  letI : Module.Finite (Base R c) (Order R c) := (ThreeRootOrder318.finite_free _).1
  exact IsNoetherianRing.of_finite (Base R c) (Order R c)

theorem localization_domain (hR : Function.Injective (algebraMap R ℚ))
    (P : Ideal (Order R c)) [P.IsPrime] : IsDomain (Localization.AtPrime P) := by
  letI := order_domain R c hR
  infer_instance

/-- Actual local DVR at every height-one prime of the whole infinity chart,
with no supplied domain, normality, or DVR on a selected component. -/
theorem localization_dvr (hR : Function.Injective (algebraMap R ℚ))
    (h2 : IsUnit (2 : R)) (P : Ideal (Order R c)) [P.IsPrime] (hP : P.height=1) :
    letI := localization_domain R c hR P
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  letI := order_domain R c hR
  letI := order_normal R c hR h2
  letI := order_noetherian R c
  exact HeightOneDVR318.localization P hP
end IntegralInfinityHeightOne318
