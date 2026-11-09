module
public import IntegralContactWholeFiber318
public import IntegralContactReduced318
public import EtaleHeightOneLocal318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public section
noncomputable section
namespace IntegralContactVerticalDVR318
open IntegralContactOpenFrame318 IsLocalRing Polynomial
open scoped nonZeroDivisors
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local instance baseDomain : IsDomain (Base R) := IntegralContactReduced318.base_domain R
local instance baseNoetherian : IsNoetherianRing (Base R) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (denominator R)) (Base R) inferInstance
local instance baseNormal : IsIntegrallyClosed (Base R) := by
  apply isIntegrallyClosed_of_isLocalization (Base R) (Submonoid.powers (denominator R))
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (pow_ne_zero n (IntegralContactReduced318.denominator_ne_zero R))

@[expose] def verticalPrime (pi : R) : Ideal (Base R) :=
  Ideal.span ({algebraMap R (Base R) pi} : Set (Base R))

theorem base_injective : Function.Injective (algebraMap R (Base R)) := by
  have hreg : Submonoid.powers (denominator R) ≤ nonZeroDivisors R[X] := by
    rintro _ ⟨n,rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero n (IntegralContactReduced318.denominator_ne_zero R))
  have h := (IsLocalization.injective (Base R) hreg).comp
    (Polynomial.C_injective : Function.Injective (Polynomial.C : R →+* R[X]))
  exact h

theorem coefficient_prime (pi : R) (hp : Irreducible pi) :
    (Ideal.span ({pi} : Set R)).IsPrime := by
  rw [← hp.maximalIdeal_eq]
  infer_instance

theorem vertical_prime (pi : R) (hp : Irreducible pi) : (verticalPrime R pi).IsPrime := by
  letI : (Ideal.span ({pi} : Set R)).IsPrime := coefficient_prime R pi hp
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  have h := IntegralContactWholeFiber318.base_fiber_domain R (Ideal.span ({pi} : Set R))
  have he : (Ideal.span ({pi} : Set R)).map (algebraMap R (Base R)) =
      verticalPrime R pi := by
    rw [Ideal.map_span, Set.image_singleton]
    all_goals rfl
  exact he ▸ h

theorem vertical_height (pi : R) (hp : Irreducible pi) : (verticalPrime R pi).height = 1 := by
  have hn : algebraMap R (Base R) pi ≠ 0 := by
    simpa only [map_zero] using (base_injective R).ne hp.ne_zero
  have hu : ¬IsUnit (algebraMap R (Base R) pi) := by
    intro h
    apply (vertical_prime R pi hp).ne_top
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_span_singleton_self _) h
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hn) hu

variable (c : Fin 4 → Rˣ) (h2 : IsUnit (2 : R)) (pi : R) (hp : Irreducible pi)
  (P : Ideal (Order R c)) [P.IsPrime] [P.LiesOver (verticalPrime R pi)]

include h2 pi hp in
/-- Actual vertical generic-point local domain, even for a split source order. -/
theorem local_domain : IsDomain (Localization.AtPrime P) := by
  letI : (verticalPrime R pi).IsPrime := vertical_prime R pi hp
  letI : Algebra.Etale (Base R) (Order R c) := (finite_free_etale R c h2).2.2
  exact EtaleHeightOneLocal318.local_domain (Base R) (Order R c) (verticalPrime R pi) P
    (vertical_height R pi hp)

/-- The vertical local ring is constructed as a DVR, not assumed to be one. -/
theorem local_dvr :
    letI := local_domain R c h2 pi hp P
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  letI : (verticalPrime R pi).IsPrime := vertical_prime R pi hp
  letI : Algebra.Etale (Base R) (Order R c) := (finite_free_etale R c h2).2.2
  exact EtaleHeightOneLocal318.local_dvr (Base R) (Order R c) (verticalPrime R pi) P
    (vertical_height R pi hp)

end IntegralContactVerticalDVR318
