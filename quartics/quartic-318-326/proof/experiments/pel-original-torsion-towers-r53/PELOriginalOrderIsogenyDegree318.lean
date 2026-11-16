module
public import ConnectedFiniteFlatFiberRank318
public import PELOriginalOrderKernelSplit318
public import PELOriginalProperSmoothGroup318
public section
noncomputable section
namespace PELOriginalOrderIsogenyDegree318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalOrderSchemeMorphism318
open PELOriginalOrderIntegralNorm318
variable (τ : ℂ) (hτ : 0<τ.im) (a : order) (ha : norm a≠0)
include ha in
/-- The native finite-flat SCHEME rank, at EVERY prime of the actual
original candidate, is the square of the actual reduced norm. -/
lemma degree (y : candidate τ hτ) :
    (morphism τ hτ a).finrank y=(norm a).natAbs^2 := by
  letI := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  letI := PELOriginalEtaleOrderIsogeny318.etale τ hτ a ha
  letI : ConnectedSpace (candidate τ hτ) :=
    (PELOriginalProperSmoothGroup318.geometric_properties τ hτ).2.2.2
  rw [ConnectedFiniteFlatFiberRank318.rank_eq_fiber
    (morphism τ hτ a) (PELOriginalSchemeGroupUnitInverse318.zeroPoint τ hτ)]
  exact PELOriginalOrderKernelSplit318.length τ hτ a ha

include ha in
/-- Degree is preserved on every literal base change, including tests
with nilpotents and disconnected tests. -/
lemma baseChange_degree {T : Scheme} (p : T⟶candidate τ hτ) (t : T) :
    (pullback.snd (morphism τ hτ a) p).finrank t=(norm a).natAbs^2 := by
  letI := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  letI := PELOriginalEtaleOrderIsogeny318.etale τ hτ a ha
  rw [Scheme.Hom.finrank_pullback_snd]
  exact degree τ hτ a ha _

include ha in
/-- Native rank-one criterion for the SAME actual order morphism. -/
lemma isIso_iff : IsIso (morphism τ hτ a) ↔ (norm a).natAbs^2=1 := by
  letI := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  letI := PELOriginalEtaleOrderIsogeny318.etale τ hτ a ha
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  constructor
  · intro h
    have h0 := congrFun h
      (PELOriginalSchemeGroupUnitInverse318.zeroPoint τ hτ (IsLocalRing.closedPoint ℂ))
    simpa only [degree τ hτ a ha,Pi.one_apply] using h0
  · intro h
    funext y
    simpa only [Pi.one_apply,h] using degree τ hτ a ha y
end PELOriginalOrderIsogenyDegree318
