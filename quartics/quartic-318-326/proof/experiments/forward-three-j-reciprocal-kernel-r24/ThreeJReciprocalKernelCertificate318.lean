module
public import PrincipalLocalizationIdealRecovery318
public section
noncomputable section
namespace ThreeJReciprocalKernelCertificate318
open Polynomial ThreeJRamificationIdealCharts318
set_option maxHeartbeats 1200000

/-- The literal reciprocal equation has an explicit polynomial inverse
certificate for the reciprocal coordinate in its nonreduced quotient. -/
@[expose] def inverseCoordinate : ℚ[X] := 196830*X+38263752*X^2+1162261467*X^3

theorem bezout : infinityEquation+X*inverseCoordinate=1 := by
  unfold infinityEquation inverseCoordinate ThreeJCuspDifferentialCharts318.reciprocalD
  ring

theorem coordinate_unit :
    IsUnit (Ideal.Quotient.mk (Ideal.span {infinityEquation}) (X:ℚ[X])) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk (Ideal.span {infinityEquation}) inverseCoordinate,?_⟩
  have h := congrArg (Ideal.Quotient.mk (Ideal.span {infinityEquation})) bezout
  have he : Ideal.Quotient.mk (Ideal.span {infinityEquation}) infinityEquation=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_add,map_mul,map_one,he,zero_add] using h

/-- No infinitesimal component can be hidden at reciprocal origin for the
proposed principal ideal: equality after puncturing implies entire equality
once the same quotient-unit condition is proved for the actual restricted ideal. -/
theorem recover_reciprocal_ideal (I : Ideal ℚ[X])
    (hI : IsUnit (Ideal.Quotient.mk I (X:ℚ[X])))
    (h : I.map (algebraMap ℚ[X] (Localization.Away (X:ℚ[X]))) =
      (Ideal.span {infinityEquation}).map (algebraMap ℚ[X] (Localization.Away (X:ℚ[X])))) :
    I=Ideal.span {infinityEquation} :=
  PrincipalLocalizationIdealRecovery318.eq_of_localized (B:=Localization.Away (X:ℚ[X]))
    X I (Ideal.span {infinityEquation}) hI coordinate_unit h
end ThreeJReciprocalKernelCertificate318
