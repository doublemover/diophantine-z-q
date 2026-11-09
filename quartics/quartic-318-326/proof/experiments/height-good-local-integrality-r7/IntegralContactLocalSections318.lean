module
public import IntegralContactWholeFiber318
public import LocalizedBaseTensorSections318
public section
noncomputable section
namespace IntegralContactLocalSections318
open IntegralContactOpenFrame318
open scoped TensorProduct
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 500000
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
  (P : Ideal (Order R c)) [P.IsPrime]
  [IsDomain (Localization.AtPrime P)] [IsDiscreteValuationRing (Localization.AtPrime P)]
  (K : Type*) [Field K] [Algebra (Localization.AtPrime P) K] [Algebra R K]
  [IsScalarTower R (Localization.AtPrime P) K] [IsFractionRing (Localization.AtPrime P) K]

/-- Integral preimages of the original J-squared-scaled bicanonical pair at
every actual good-chart prime localization which is a DVR. Both the local
differential frame and reduced fiber are constructed, not supplied. -/
theorem integral_sections (h2 : IsUnit (2 : R)) (r : R)
    [(Ideal.span ({r} : Set R)).IsPrime]
    (hr0 : algebraMap R (Localization.AtPrime P) r ≠ 0)
    (hru : ¬IsUnit (algebraMap R (Localization.AtPrime P) r)) (t : K) :
    (∃ x0, IntegralCotangentTensor318.map (R := R) (B := Localization.AtPrime P) (K := K) (atPrimeFrame R c h2 P) x0 =
      VerticalCotangentSections318.q0 (R := R) t) ∧
    (∃ x1, IntegralCotangentTensor318.map (R := R) (B := Localization.AtPrime P) (K := K) (atPrimeFrame R c h2 P) x1 =
      VerticalCotangentSections318.q1 (R := R) t) := by
  letI : IsReduced (Order R c ⧸ Ideal.span ({algebraMap R (Order R c) r} : Set (Order R c))) :=
    IntegralContactWholeFiber318.parameter_fiber_reduced R c h2 r
  exact LocalizedBaseTensorSections318.integral_sections (R := R) (A := Order R c)
    (B := Localization.AtPrime P) (K := K) P.primeCompl
    (atPrimeFrame R c h2 P) r hr0 hru t

end IntegralContactLocalSections318
