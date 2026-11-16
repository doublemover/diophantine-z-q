module
public import PELPrincipalThreeStabilizer318
public section
noncomputable section
namespace PELPrincipalThreeFreeAction318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open QuaternionicUnitPeriodTransport318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointArithmeticLift318 PELJointArithmeticCoherence318
open PELJointNormOneAction318 PELPrincipalThreeStabilizer318
set_option maxHeartbeats 1400000

lemma three_smul (a:order) : (3:ℕ) • a=a+a+a := by
  rw [show (3:ℕ)=1+1+1 from rfl,add_nsmul,add_nsmul,one_nsmul]

/-- The literal principal congruence subgroup, with u−1 in THREE TIMES THE
ORIGINAL ORDER. Containment of this subgroup is not itself a smallness criterion. -/
@[expose] def congruentOneThree : Subgroup orderˣ where
  carrier := {u | ∃ v : order,(u:order)=1+(3:ℕ) • v}
  one_mem' := ⟨0,by simp⟩
  mul_mem' := by
    rintro u v ⟨a,ha⟩ ⟨b,hb⟩
    refine ⟨a+b+(3:ℕ) • (a*b),?_⟩
    change (u:order)*(v:order)=_
    rw [ha,hb]
    simp only [three_smul]
    noncomm_ring
  inv_mem' := by
    rintro u ⟨a,ha⟩
    refine ⟨-((↑u⁻¹:order)*a),?_⟩
    change (↑u⁻¹:order)=_
    calc
      _ = (↑u⁻¹:order)*(u:order)-(3:ℕ) • ((↑u⁻¹:order)*a) := by
        rw [ha]
        simp only [three_smul]
        noncomm_ring
      _ = 1+(3:ℕ) • (-((↑u⁻¹:order)*a)) := by
        have hunit : (↑u⁻¹:order)*(u:order)=1 :=
          congrArg (fun w:orderˣ=>(w:order)) (inv_mul_cancel u)
        rw [hunit]
        simp only [three_smul]
        noncomm_ring

@[expose] def principalThree : Subgroup orderˣ := normOneUnits ⊓ congruentOneThree

theorem determinant (u : principalThree) : (unitMatrix representation order u.val).det=1 :=
  u.property.1

/-- No original principal-three unit other than1 fixes an upper-half-plane
parameter. This proves the SPECIFIC level-three stabilizer statement. -/
theorem no_base_stabilizer (u : principalThree) (τ : HalfPlane)
    (h : nextParameter u.val (determinant u) τ=τ) : u=1 := by
  obtain ⟨v,hv⟩ := u.property.2
  apply Subtype.ext
  exact fixed_implies_one u.val ((mem_normOneUnits u.val).mp u.property.1) v hv τ τ.property
    (congrArg Subtype.val h)

instance : MulAction principalThree Total where
  smul u p := totalAction u.val (determinant u) p
  one_smul p := total_one p
  mul_smul u v p := (total_mul u.val v.val (determinant u) (determinant v) p).symm

/-- The actual action on the joint family is free as a consequence of its
base action, not an assumed fine-moduli or torsion-free marking assertion. -/
theorem no_total_stabilizer (u : principalThree) (p : Total) (h : u • p=p) : u=1 :=
  no_base_stabilizer u p.1 (congrArg Prod.fst h)

/-- Restriction to this precise subgroup retains the original projection
square. Proper discontinuity and an arithmetic quotient remain separate. -/
theorem projection_square (u : principalThree) (p : Cover) :
    u • familyProjection p=familyProjection (lift u.val (determinant u) p) :=
  PELJointArithmeticLift318.projection_square u.val (determinant u) p
end PELPrincipalThreeFreeAction318
