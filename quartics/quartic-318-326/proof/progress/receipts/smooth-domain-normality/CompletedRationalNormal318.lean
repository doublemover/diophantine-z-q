module
public import SmoothDomainNormal318
public import CompletedIntegral318
public import InfinitySmooth318
public section
noncomputable section
namespace CompletedRationalNormal318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Normality of the entire actual finite affine chart, not just a Jacobian open. -/
theorem affine (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsIntegrallyClosed (ShortAffineJacobian318.Ring A B) := by
  letI:=AffineCoordinateDomain318.affine_domain A B
  letI:=ShortAffineJacobian318.smooth A B hD
  exact SmoothDomainNormal318.integrallyClosed ℚ (ShortAffineJacobian318.Ring A B)

/-- Normality of the entire actual infinity chart, including its full origin neighborhood. -/
theorem infinity (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsIntegrallyClosed (InfinityChart318.Ring A B) := by
  letI:=InfinityCoordinateDomain318.infinity_domain A B
  letI:=InfinitySmooth318.smooth A B hD
  exact SmoothDomainNormal318.integrallyClosed ℚ (InfinityChart318.Ring A B)

theorem both_charts (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsIntegrallyClosed (ShortAffineJacobian318.Ring A B) ∧
    IsIntegrallyClosed (InfinityChart318.Ring A B) := ⟨affine A B hD,infinity A B hD⟩
end CompletedRationalNormal318
