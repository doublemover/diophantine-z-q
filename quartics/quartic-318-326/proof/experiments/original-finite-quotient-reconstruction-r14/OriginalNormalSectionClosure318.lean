module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace OriginalNormalSectionClosure318
variable (R A K : Type*) [CommRing R] [CommRing A] [IsDomain A] [Field K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
  [IsFractionRing A K] [IsIntegrallyClosed A] [Algebra.IsIntegral R A]

/-- Actual normal integral sections exhaust the integral closure inside their
SAME fraction field. No abstract replacement embedding is selected. -/
theorem isIntegralClosure : IsIntegralClosure A R K :=
  IsIntegralClosure.of_isIntegrallyClosedIn

@[expose] def equivalence : A ≃ₐ[R] integralClosure R K := by
  letI := isIntegralClosure R A K
  exact IsIntegralClosure.equiv R A K (integralClosure R K)

lemma equivalence_embedding (a : A) :
    algebraMap (integralClosure R K) K (equivalence R A K a) = algebraMap A K a := by
  letI := isIntegralClosure R A K
  exact IsIntegralClosure.algebraMap_equiv R A K (integralClosure R K) a

lemma equivalence_base (r : R) :
    equivalence R A K (algebraMap R A r) = algebraMap R (integralClosure R K) r :=
  (equivalence R A K).commutes r
end OriginalNormalSectionClosure318
