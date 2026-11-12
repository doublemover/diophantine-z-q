module
public import IntegralTwoChartNormalization318
public import HeightOneDVR318
public import ActualDVRCompletion318
public import CompletionDescent318
public section
noncomputable section
namespace IntegralNormalModelCodimensionOne318
open Polynomial CategoryTheory AlgebraicGeometry IntegralReciprocalBase318
open IntegralTwoChartNormalization318
set_option maxHeartbeats 1000000
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]]
  (a : Fin 4 → R) (N : R) (B : Type u) [CommRing B] [IsDomain B]
  [Algebra (FiniteBase R a N) B] [Module.Finite (FiniteBase R a N) B]
  [Algebra.Etale (FiniteBase R a N) B]
  (hN : N ≠ 0) (j : Fin 2) (x : (sourceCover R a N B j).1)
  (hx : ((sourceCover R a N B j).2.primeIdealOf x).asIdeal.height = 1)

include hN hx in
/-- Every actual height-one chart point of the constructed arithmetic
surface has a DVR stalk. This does not assert regularity at closed
codimension-two centers, even when a proper valuative section meets them. -/
theorem stalk_dvr : IsDiscreteValuationRing ((model R a N B).presheaf.stalk x.val) := by
  letI : IsIntegral (model R a N B) := model_integral R a N B
  let U := sourceCover R a N B j
  let A := Γ(model R a N B,U)
  let S := (model R a N B).presheaf.stalk x.val
  let p := (U.2.primeIdealOf x).asIdeal
  letI : IsDomain A := (chart_properties R a N B hN j).1
  letI : IsIntegrallyClosed A := (chart_properties R a N B hN j).2.1
  letI : IsNoetherianRing A := (chart_properties R a N B hN j).2.2
  letI := (model R a N B).presheaf.algebra_section_stalk x
  letI := U.2.isLocalization_stalk x
  letI := HeightOneDVR318.localization p hx
  let e : Localization.AtPrime p ≃ₐ[A] S := IsLocalization.algEquiv p.primeCompl _ _
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

/-- Completion uses the actual maximal ideal of the actual global scheme
stalk, not a chosen abstract complete DVR with the same residue field. -/
theorem completed_stalk :
    let S := (model R a N B).presheaf.stalk x.val
    letI : IsIntegral (model R a N B) := model_integral R a N B
    letI := stalk_dvr R a N B hN j x hx
    IsDiscreteValuationRing (ActualDVRCompletion318.Completion S) ∧
    Module.FaithfullyFlat S (ActualDVRCompletion318.Completion S) ∧
    Function.Injective (algebraMap S (ActualDVRCompletion318.Completion S)) := by
  let S := (model R a N B).presheaf.stalk x.val
  letI : IsIntegral (model R a N B) := model_integral R a N B
  letI := stalk_dvr R a N B hN j x hx
  exact ⟨inferInstance,CompletionDescent318.completion_faithfullyFlat S,
    ActualDVRCompletion318.completion_injective S⟩
end IntegralNormalModelCodimensionOne318
