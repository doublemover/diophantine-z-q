module
public import PELJointArithmeticHolomorphy318
public section
noncomputable section
namespace PELJointArithmeticCoherence318
open QuaternionicRealPeriod318 QuaternionicUnitPeriodTransport318 QuaternionicPeriodAutomorphy318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open PELJointComplexAtlas318 PELJointArithmeticLift318 PELJointArithmeticHolomorphy318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

lemma determinant_one : (unitMatrix representation order (1:orderˣ)).det=1 := by
  simp [unitMatrix]
lemma determinant_mul (u v : orderˣ) (hu : (unitMatrix representation order u).det=1)
    (hv : (unitMatrix representation order v).det=1) :
    (unitMatrix representation order (u*v)).det=1 := by
  rw [unitMatrix_mul,Matrix.det_mul,hu,hv,mul_one]
lemma determinant_inv (u : orderˣ) (hu : (unitMatrix representation order u).det=1) :
    (unitMatrix representation order u⁻¹).det=1 := by
  have h := congrArg Matrix.det (unitMatrix_mul_inv representation order u)
  simpa only [Matrix.det_mul,hu,one_mul,Matrix.det_one] using h

theorem lift_mul (u v : orderˣ) (hu : (unitMatrix representation order u).det=1)
    (hv : (unitMatrix representation order v).det=1) (p : Cover) :
    lift u hu (lift v hv p)=lift (u*v) (determinant_mul u v hu hv) p := by
  apply Prod.ext
  · apply Subtype.ext
    exact unit_parameter_comp representation order u v hu hv p.1 p.1.property
  · exact unit_scalar_cocycle representation order u v hv p.1 p.1.property p.2

theorem lift_one (p : Cover) : lift 1 determinant_one p=p := by
  apply Prod.ext
  · apply Subtype.ext
    simp [lift,nextParameter,PELOriginalUnitBiholomorph318.parameter,unitParameter,
      QuaternionicMobiusPeriods318.mobius,QuaternionicMobiusPeriods318.denominator,unitMatrix]
  · simp [lift,unitDenominator,QuaternionicMobiusPeriods318.denominator,unitMatrix]

/-- The action law is proved on the JOINT total space by its surjective
original projection and exact covering-map square, not by relabeling fibers. -/
theorem total_mul (u v : orderˣ) (hu : (unitMatrix representation order u).det=1)
    (hv : (unitMatrix representation order v).det=1) (p : Total) :
    totalAction u hu (totalAction v hv p)=totalAction (u*v) (determinant_mul u v hu hv) p := by
  obtain ⟨a,rfl⟩ := familyProjection_surjective p
  rw [projection_square,projection_square,lift_mul,projection_square]

theorem total_one (p : Total) : totalAction 1 determinant_one p=p := by
  obtain ⟨a,rfl⟩ := familyProjection_surjective p
  rw [projection_square,lift_one]

theorem total_inverse_left (u : orderˣ) (hu : (unitMatrix representation order u).det=1)
    (p : Total) : totalAction u⁻¹ (determinant_inv u hu) (totalAction u hu p)=p := by
  rw [total_mul]
  simpa only [inv_mul_cancel] using total_one p

theorem total_inverse_right (u : orderˣ) (hu : (unitMatrix representation order u).det=1)
    (p : Total) : totalAction u hu (totalAction u⁻¹ (determinant_inv u hu) p)=p := by
  rw [total_mul]
  simpa only [mul_inv_cancel] using total_one p

/-- Actual holomorphic automorphisms of the same joint family. The inverse
is the original inverse order unit; no separate existence choice is used. -/
@[expose] def totalEquiv (u : orderˣ) (hu : (unitMatrix representation order u).det=1) : Total ≃ Total where
  toFun := totalAction u hu
  invFun := totalAction u⁻¹ (determinant_inv u hu)
  left_inv := total_inverse_left u hu
  right_inv := total_inverse_right u hu

theorem totalEquiv_holomorphic (u : orderˣ) (hu : (unitMatrix representation order u).det=1) :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (totalEquiv u hu) := totalAction_holomorphic u hu

theorem totalEquiv_inverse_holomorphic (u : orderˣ) (hu : (unitMatrix representation order u).det=1) :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (totalEquiv u hu).symm :=
  totalAction_holomorphic u⁻¹ (determinant_inv u hu)
end PELJointArithmeticCoherence318
