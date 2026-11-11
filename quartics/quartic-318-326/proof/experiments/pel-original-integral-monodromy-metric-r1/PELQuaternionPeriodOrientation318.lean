module
public import QuaternionicPeriodAlternating318
public import PELQuaternionRealRepresentation318
public section
noncomputable section
namespace PELQuaternionPeriodOrientation318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 QuaternionicRealPeriod318
set_option maxHeartbeats 1200000

/-- Exact agreement with the ORIGINAL μ-oriented rational trace pairing,
including its sign and the scale sqrt210. -/
theorem original_pairing (x y : B) :
    QuaternionicPeriodAlternating318.pairing (representation x) (representation y)=
      (PELQuaternionAlternatingForm318.pairing x y:ℝ) := by
  rw [PELQuaternionAlternatingForm318.coordinates]
  change (((x.re:ℝ)+beta*(x.imJ:ℝ))*(-alpha*(y.imI:ℝ)+alpha*beta*(y.imK:ℝ))-
    (-alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ))*((y.re:ℝ)+beta*(y.imJ:ℝ))+
    ((alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ))*((y.re:ℝ)-beta*(y.imJ:ℝ))-
    ((x.re:ℝ)-beta*(x.imJ:ℝ))*(alpha*(y.imI:ℝ)+alpha*beta*(y.imK:ℝ))))/alpha=_
  push_cast
  field_simp [alpha_pos.ne']
  <;> ring_nf
  <;> simp only [beta_sq]
  <;> ring

/-- Positivity of the period-oriented form is an actual compatibility with
our precise quaternion representation and our precise complex structure. -/
theorem period_positive (τ : ℂ) (hτ : 0<τ.im) (x : B) (hx : x≠0) :
    0<QuaternionicPeriodAlternating318.oriented (representation x)
      (complexStructure τ hτ (representation x)) := by
  apply QuaternionicPeriodAlternating318.oriented_positive τ hτ
  intro h
  apply hx
  apply representation_injective
  simpa only [map_zero] using h

/-- The chosen μ form has the opposite orientation for E(v,Jv). This is
retained as an explicit theorem rather than hidden by renaming the pairing. -/
theorem original_period_negative (τ : ℂ) (hτ : 0<τ.im) (x : B) (hx : x≠0) :
    QuaternionicPeriodAlternating318.pairing (representation x)
      (complexStructure τ hτ (representation x))<0 := by
  apply QuaternionicPeriodAlternating318.original_negative τ hτ
  intro h
  apply hx
  apply representation_injective
  simpa only [map_zero] using h

/-- Negation changes no adjoint action: the same positive Rosati involution
is compatible with the period-oriented alternating form. -/
theorem oriented_left_adjoint (a x y : B) :
    QuaternionicPeriodAlternating318.oriented (representation (a*x)) (representation y)=
      QuaternionicPeriodAlternating318.oriented (representation x) (representation (rosati a*y)) := by
  simp only [QuaternionicPeriodAlternating318.oriented,original_pairing,
    PELQuaternionAlternatingForm318.left_action_adjoint]
end PELQuaternionPeriodOrientation318
