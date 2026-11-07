module
public import ActualQJ318
public section
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
namespace ActualJInvariant318
set_option maxHeartbeats 0

/-- The normalized analytic function used in the producer is genuinely
invariant under the actual integral modular-group image in GL(2,R). -/
theorem modular_invariant (gamma:GL (Fin 2) ℝ)
    (hgamma:gamma∈(Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ).range) (tau:UpperHalfPlane) :
    ActualQJ318.jInvariant (gamma • tau)=ActualQJ318.jInvariant tau := by
  have he:=SlashInvariantForm.slash_action_eqn''
    (Γ:=(Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ).range)
    (ModularForm.E (k:=4) (by norm_num)) hgamma tau
  have hd:=SlashInvariantForm.slash_action_eqn''
    (Γ:=(Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ).range)
    CuspForm.discriminant hgamma tau
  norm_num only [CuspForm.coe_discriminant,Nat.cast_ofNat,zpow_ofNat] at he hd
  unfold ActualQJ318.jInvariant
  rw [he,hd]
  have hden:=denom_ne_zero gamma tau
  field_simp

end ActualJInvariant318
#print axioms ActualJInvariant318.modular_invariant
