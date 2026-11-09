module
public import IntegralContactVerticalDVR318
public import IntegralContactLocalSections318
public section
noncomputable section
namespace IntegralContactActualVertical318
open IntegralContactOpenFrame318 IntegralContactVerticalDVR318
open scoped TensorProduct
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (c : Fin 4 → Rˣ) (h2 : IsUnit (2 : R)) (pi : R) (hp : Irreducible pi)
  (P : Ideal (Order R c)) [P.IsPrime] [P.LiesOver (verticalPrime R pi)]
  (K : Type*) [Field K] [Algebra (Localization.AtPrime P) K] [Algebra R K]
  [IsScalarTower R (Localization.AtPrime P) K] [IsFractionRing (Localization.AtPrime P) K]

/-- End-to-end actual vertical integrality on the good-contact chart.
The source DVR, local differential frame, reduced fiber, and nonzero/nonunit
base parameter are all constructed. The only chosen vertical prime lies over
the explicit generic point of the arithmetic special fiber. -/
theorem integral_sections (t : K) :
    letI := local_domain R c h2 pi hp P
    (∃ x0, IntegralCotangentTensor318.map (R := R) (B := Localization.AtPrime P) (K := K) (atPrimeFrame R c h2 P) x0 =
      VerticalCotangentSections318.q0 (R := R) t) ∧
    (∃ x1, IntegralCotangentTensor318.map (R := R) (B := Localization.AtPrime P) (K := K) (atPrimeFrame R c h2 P) x1 =
      VerticalCotangentSections318.q1 (R := R) t) := by
  letI : IsDomain (Base R) := IntegralContactReduced318.base_domain R
  letI : IsDomain (Localization.AtPrime P) := local_domain R c h2 pi hp P
  letI : IsDiscreteValuationRing (Localization.AtPrime P) := local_dvr R c h2 pi hp P
  letI : Module.Free (Base R) (Order R c) := (finite_free_etale R c h2).2.1
  letI : (Ideal.span ({pi} : Set R)).IsPrime := coefficient_prime R pi hp
  letI : Module.Flat (Base R) (Localization.AtPrime P) :=
    Module.Flat.trans (Base R) (Order R c) (Localization.AtPrime P)
  have hinj : Function.Injective (algebraMap (Base R) (Localization.AtPrime P)) :=
    FaithfulSMul.algebraMap_injective (Base R) (Localization.AtPrime P)
  have hb0 : algebraMap R (Base R) pi ≠ 0 := by
    simpa only [map_zero] using (base_injective R).ne hp.ne_zero
  have hr0 : algebraMap R (Localization.AtPrime P) pi ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R (Base R) (Localization.AtPrime P)]
    simpa only [map_zero] using hinj.ne hb0
  have hm : algebraMap R (Base R) pi ∈ P.under (Base R) := by
    rw [← Ideal.LiesOver.over (P := P) (p := verticalPrime R pi)]
    exact Ideal.mem_span_singleton_self _
  have hsource : algebraMap R (Order R c) pi ∈ P := by
    rw [IsScalarTower.algebraMap_apply R (Base R) (Order R c)]
    exact hm
  have hru : ¬IsUnit (algebraMap R (Localization.AtPrime P) pi) := by
    rw [IsScalarTower.algebraMap_apply R (Order R c) (Localization.AtPrime P)]
    intro hu
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).mp hu) hsource
  exact IntegralContactLocalSections318.integral_sections R c P K h2 pi hr0 hru t

end IntegralContactActualVertical318
