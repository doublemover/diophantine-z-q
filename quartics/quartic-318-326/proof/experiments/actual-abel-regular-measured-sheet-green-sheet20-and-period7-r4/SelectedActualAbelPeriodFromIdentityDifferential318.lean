module

public import SelectedActualAbelPeriodAgreement318
public import SelectedActualAbelIdentityChartLifts318
import all SelectedActualAbelPeriodAgreement318
public import Mathlib.Analysis.Calculus.FDeriv.Prod

public section

noncomputable section

open UpperHalfPlane Metric Set Function
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedActualOrdinaryAbelPeriodMap318
open SelectedActualAbelPeriodAgreement318 SelectedActualAbelIdentityChartLifts318

namespace SelectedActualAbelPeriodFromIdentityDifferential318

variable {M g : ℕ} {J : Type*} [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]

/-- Read the actual Abel map on the literal old period quotient from the
same algebraic source's local analytic invariant differential. -/
def readAbel (a : Base (image M) → J) (z : ℂ) : J :=
  a (quotientMap M (UpperHalfPlane.ofComplex z))

/-- This is the invariant differential of the given map, read via
translation to the identity in the same target. It does not assert
existence, differentiability, or period descent of a logarithm lift. -/
def InvariantDifferentialEquation (f : Fin g → Form M)
    {q : (Fin g → ℂ) →+ J} (C : IdentityChart q) (a : Base (image M) → J) : Prop :=
  ∀ z ∈ upperHalfPlaneSet,
    HasDerivAt (fun w => C.coord (readAbel a w - readAbel a z))
      (fun i => f i (UpperHalfPlane.ofComplex z)) z

theorem actual_local_original_lifts (hM : 5 ≤ M)
    (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J) (hq : Continuous q) (hqS : Surjective q)
    (C : IdentityChart q) (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f C a) :
    LocalOriginalLifts f q a := by
  have hcont : ContinuousOn (readAbel a) upperHalfPlaneSet := by
    intro z hz
    have h₁ : ContinuousAt (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane) z :=
      (UpperHalfPlane.mdifferentiableAt_ofComplex hz).continuousAt
    have h₂ : Continuous (quotientMap M) := (GammaOneAtlas318.quotient_localHomeomorph M hM).continuous
    exact (ha.continuousAt.comp (h₂.continuousAt.comp h₁)).continuousWithinAt
  unfold LocalOriginalLifts
  intro τ
  obtain ⟨r,hr,hU,P,hval,hder⟩ := exists_disk_lift q hq hqS C (readAbel a)
    upperHalfPlaneSet isOpen_upperHalfPlaneSet hcont
    (fun z i => f i (UpperHalfPlane.ofComplex z)) hread (τ : ℂ) τ.im_pos
  refine ⟨r,hr,hU,fun i z => P z i,?_,hval⟩
  intro i z hz
  let p : (Fin g → ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i
  exact p.hasFDerivAt.comp_hasDerivAt z (hder z hz)

/-- Period descent and same-map compatibility from the actual invariant
differential equation, with no period-kernel hypothesis. -/
theorem period_zero_of_invariant_differential (hM : 5 ≤ M)
    (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J) (hq : Continuous q) (hqS : Surjective q)
    (C : IdentityChart q) (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f C a) (γ : image M) :
    q (modularPeriod f γ) = 0 :=
  periods_zero_of_original_lifts f q a (actual_local_original_lifts hM f q hq hqS C a ha hread) γ

theorem same_original_map_of_invariant_differential (hM : 5 ≤ M)
    (f : Fin g → Form M) (q : (Fin g → ℂ) →+ J) (hq : Continuous q) (hqS : Surjective q)
    (C : IdentityChart q) (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f C a) :
    a = fun x => ordinaryAbel f q (period_zero_of_invariant_differential hM f q hq hqS C a ha hread) x +
      a (quotientMap M UpperHalfPlane.I) :=
  original_map_is_period_map f q a (actual_local_original_lifts hM f q hq hqS C a ha hread)

end SelectedActualAbelPeriodFromIdentityDifferential318

#print axioms SelectedActualAbelPeriodFromIdentityDifferential318.actual_local_original_lifts
#print axioms SelectedActualAbelPeriodFromIdentityDifferential318.same_original_map_of_invariant_differential
