module
public import EtalePrimeDVR318
public section
noncomputable section
namespace EvenContactBranch318
set_option maxHeartbeats 800000
open IsLocalRing
variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (u:Rˣ) (h2:IsUnit (2:R))
include h2

/-- Every prime of the ACTUAL constructed unit-root normalization is unramified
and has actual ramification index one. No etaleness premise is supplied. -/
theorem all_prime_indices (q:Ideal (EvenContactEtale318.RootRing u)) [q.IsPrime] :
    Algebra.IsUnramifiedAt R q ∧ q.ramificationIdx R=1 := by
  letI:=EvenContactEtale318.rootRing_etale u h2
  exact ⟨inferInstance,Ideal.ramificationIdx_eq_one q R⟩

variable (q:Ideal (EvenContactEtale318.RootRing u)) [q.IsPrime]
  [q.LiesOver (maximalIdeal R)]

/-- Each genuine local branch of a possibly split normalization is a domain. -/
theorem branch_domain : IsDomain (Localization.AtPrime q) := by
  letI:=EvenContactEtale318.rootRing_etale u h2
  exact EtalePrimeDVR318.local_domain R (EvenContactEtale318.RootRing u) q

/-- Its DVR structure is derived, rather than identifying a split quadratic
algebra globally with a field or a domain. -/
theorem branch_dvr :
    letI:=branch_domain u h2 q
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  letI:=EvenContactEtale318.rootRing_etale u h2
  exact EtalePrimeDVR318.local_dvr R (EvenContactEtale318.RootRing u) q

/-- Every source canonical valuation is exactly preserved in every branch. -/
theorem branch_value (x:R) :
    letI:=branch_domain u h2 q
    letI:=branch_dvr u h2 q
    IsDiscreteValuationRing.addVal (Localization.AtPrime q)
      (algebraMap R (Localization.AtPrime q) x)=IsDiscreteValuationRing.addVal R x := by
  letI:=EvenContactEtale318.rootRing_etale u h2
  exact EtalePrimeDVR318.local_value R (EvenContactEtale318.RootRing u) q x

/-- The actual residue-field extension at each closed branch is finite separable. -/
theorem branch_residue :
    letI:=EvenContactEtale318.rootRing_etale u h2
    letI:=EtalePrimeDVR318.localMap R (EvenContactEtale318.RootRing u) q
    Module.Finite (ResidueField R) (ResidueField (Localization.AtPrime q)) ∧
      Algebra.IsSeparable (ResidueField R) (ResidueField (Localization.AtPrime q)) := by
  letI:=EvenContactEtale318.rootRing_etale u h2
  exact EtalePrimeDVR318.residue_data R (EvenContactEtale318.RootRing u) q

end EvenContactBranch318
