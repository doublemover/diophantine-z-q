module
public import IntegralArithmeticBranchNormal318
public import HeightOneDVR318
public import AffineHeightOneStalk318
public section
noncomputable section
namespace IntegralArithmeticHeightOne318
open IntegralSourceBranches318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] [IsDomain R] [Algebra R ℚ]
  [IsIntegrallyClosed R] [IsNoetherianRing R] (c : Fin 4 → Rˣ)

/-- Noetherianity is supplied by the actual finite-free monic source order
over the polynomial algebra of the original arithmetic base. -/
theorem source_noetherian : IsNoetherianRing (SourceOrder R c) := by
  letI : Module.Finite R[X] (SourceOrder R c) :=
    (FourRootOrder318.finite_free (coefficient R c)).1
  exact IsNoetherianRing.of_finite R[X] (SourceOrder R c)

theorem localization_domain (hR : Function.Injective (algebraMap R ℚ))
    (P : Ideal (SourceOrder R c)) [P.IsPrime] : IsDomain (Localization.AtPrime P) := by
  letI := IntegralSourceArithmeticDomain318.source_domain R c hR
  infer_instance

/-- Every actual height-one prime of the whole original arithmetic source
has a genuine DVR local ring. Domain, normality and Noetherianity are all
constructed from the arithmetic base and the original good-chart cover. -/
theorem localization_dvr (hR : Function.Injective (algebraMap R ℚ))
    (h2 : IsUnit (2 : R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R))
    (P : Ideal (SourceOrder R c)) [P.IsPrime] (hP : P.height=1) :
    letI := localization_domain R c hR P
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  letI := IntegralSourceArithmeticDomain318.source_domain R c hR
  letI := IntegralArithmeticBranchNormal318.source_normal R c hR h2 hN
  letI := source_noetherian R c
  exact HeightOneDVR318.localization P hP

/-- The same construction supplies the actual structure-sheaf stalk at every original codimension-one affine point, not a substitute
abstract valuation ring. -/
theorem stalk_dvr (hR : Function.Injective (algebraMap R ℚ))
    (h2 : IsUnit (2 : R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R)) :
    letI := IntegralSourceArithmeticDomain318.source_domain R c hR
    letI := IntegralArithmeticBranchNormal318.source_normal R c hR h2 hN
    letI := source_noetherian R c
    ∀ x : AffineHeightOneStalk318.Point (SourceOrder R c),
      IsDiscreteValuationRing (AffineHeightOneStalk318.Stalk (SourceOrder R c) x) := by
  letI := IntegralSourceArithmeticDomain318.source_domain R c hR
  letI := IntegralArithmeticBranchNormal318.source_normal R c hR h2 hN
  letI := source_noetherian R c
  intro x
  exact AffineHeightOneStalk318.stalk_dvr _ x
end IntegralArithmeticHeightOne318
