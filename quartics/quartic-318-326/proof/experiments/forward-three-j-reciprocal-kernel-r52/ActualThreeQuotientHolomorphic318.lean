module
public import ActualThreeHolomorphicDescent318
public section
noncomputable section
open Function Filter Topology
namespace ActualThreeQuotientHolomorphic318
open ActualThreeExceptionalParameter318 ActualThreeGlobalParameter318 ActualThreeHolomorphicDescent318
open GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A complex-valued function is quotient-holomorphic at an original quotient
point if its pullback along the original orbit projection is holomorphic at
every representative. This definition does not use the target parameter. -/
@[expose] def QuotientHolomorphicAt (u : Base (image 3) → ℂ) (b : Base (image 3)) : Prop :=
  ∀ tau : UpperHalfPlane, quotientMap 3 tau=b →
    AnalyticAt ℂ (fun z : ℂ => u (quotientMap 3 (UpperHalfPlane.ofComplex z))) (tau:ℂ)

/-- The expression of an original quotient function in the already proved
original global T coordinate; its arbitrary value at zero is outside C*. -/
@[expose] def parameterExpression (u : Base (image 3) → ℂ) (t : ℂ) : ℂ :=
  if ht : t ≠ 0 then u (globalHomeomorph.symm ⟨t,ht⟩) else 0

lemma expression_parameter (u : Base (image 3) → ℂ) (b : Base (image 3)) :
    parameterExpression u (quotientParameter b)=u b := by
  rw [parameterExpression,dite_eq_left (quotientParameter_ne_zero b)]
  change u (globalHomeomorph.symm (globalHomeomorph b))=u b
  rw [globalHomeomorph.symm_apply_apply]

lemma expression_period (u : Base (image 3) → ℂ) (tau : UpperHalfPlane) :
    parameterExpression u (periodParameter tau)=u (quotientMap 3 tau) :=
  expression_parameter u (quotientMap 3 tau)

/-- The genuine quotient-holomorphic germ condition is equivalent to ordinary
holomorphicity in the independent T target coordinate, including elliptic
points. This is proved by descent, not stipulated by transport of structure. -/
theorem quotientHolomorphicAt_iff_parameter (u : Base (image 3) → ℂ)
    (b : Base (image 3)) : QuotientHolomorphicAt u b ↔
      AnalyticAt ℂ (parameterExpression u) (quotientParameter b) := by
  constructor
  · intro hu
    obtain ⟨tau,rfl⟩ := quotient_surjective 3 b
    apply (analyticAt_iff_period_pullback (parameterExpression u) tau).mpr
    simpa only [expression_period] using hu tau rfl
  · intro hu tau ht
    have hperiod : AnalyticAt ℂ (parameterExpression u) (periodParameter tau) := by
      simpa only [←quotientParameter_projection,ht] using hu
    simpa only [expression_period] using
      (analyticAt_iff_period_pullback (parameterExpression u) tau).mp hperiod

/-- Entire original-quotient holomorphicity is exactly target C* holomorphicity
of the same function, with the original quotient projection as the consumer. -/
theorem quotientHolomorphic_iff_parameter (u : Base (image 3) → ℂ) :
    (∀ b, QuotientHolomorphicAt u b) ↔
      AnalyticOnNhd ℂ (parameterExpression u) {t : ℂ | t ≠ 0} := by
  constructor
  · intro hu t ht
    obtain ⟨b,hb⟩ := ActualThreeParameterProper318.fullParameter_surjective ⟨t,ht⟩
    have he : quotientParameter b=t := congrArg Subtype.val hb
    rw [←he]
    exact (quotientHolomorphicAt_iff_parameter u b).mp (hu b)
  · intro hu b
    exact (quotientHolomorphicAt_iff_parameter u b).mpr
      (hu _ (quotientParameter_ne_zero b))

end ActualThreeQuotientHolomorphic318
