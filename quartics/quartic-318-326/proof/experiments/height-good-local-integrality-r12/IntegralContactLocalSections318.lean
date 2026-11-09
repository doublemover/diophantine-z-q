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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Resolve the actual native ideal quotient at abstract rings, before the
-- deeply nested tensor/localization carrier is substituted. This is precisely
-- Ideal.instHasQuotient (the submodule quotient), not a new quotient object.
abbrev nativeIdealQuotient (A : Type*) [CommRing A] : HasQuotient A (Ideal A) :=
  inferInstance

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
  (P : Ideal (Order R c)) [P.IsPrime]
  [IsDomain (Localization.AtPrime P)] [IsDiscreteValuationRing (Localization.AtPrime P)]
  (K : Type*) [Field K] [Algebra (Localization.AtPrime P) K] [Algebra R K]
  [IsScalarTower R (Localization.AtPrime P) K] [IsFractionRing (Localization.AtPrime P) K]

local instance primeIdealQuotient :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  nativeIdealQuotient (Localization.AtPrime P)

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
  haveI : IsReduced (Order R c ⧸ Ideal.span ({algebraMap R (Order R c) r} : Set (Order R c))) :=
    IntegralContactWholeFiber318.parameter_fiber_reduced R c h2 r
  haveI : IsReduced (Localization.AtPrime P ⧸ Ideal.span
      ({algebraMap R (Localization.AtPrime P) r} : Set (Localization.AtPrime P))) :=
    LocalizedReducedFiber318.base_parameter_reduced (R := R) (A := Order R c)
      (B := Localization.AtPrime P) P.primeCompl r
  -- Finish over the local ring alone. The localization transport is already
  -- discharged; elaborating it again through the full explicit frame expands
  -- the four-root tensor order and its scalar towers unnecessarily.
  -- Match the conclusion first, so the already elaborated native frame is
  -- inferred from the target instead of re-elaborated against a second deep
  -- Kaehler module structure at the explicit argument site.
  apply ReducedBaseTensorSections318.integral_sections (R := R)
    (B := Localization.AtPrime P) (K := K) (r := r)
  · exact hr0
  · exact hru

end IntegralContactLocalSections318
