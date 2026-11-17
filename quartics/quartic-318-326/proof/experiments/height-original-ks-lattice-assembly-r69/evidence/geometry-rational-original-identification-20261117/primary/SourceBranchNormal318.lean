module
public import SourceBranchLocalization318
public import SmoothGenericField318
public section
noncomputable section
namespace SourceBranchNormal318
open Polynomial SourceFiniteBranch318
open scoped nonZeroDivisors
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) (i:Fin 4)

lemma branch_integrallyClosed : IsIntegrallyClosed (BranchBase c i) :=
  IsIntegrallyClosed.of_equiv
    (LinearRootCoordinate318.coordinateEquiv (c i)
      (LinearContactSquareclass318.contacts i)).symm.toRingEquiv

lemma openBase_integrallyClosed : IsIntegrallyClosed (OpenBase c i) := by
  letI:=branch_integrallyClosed c i
  letI:=FiniteBranchChart318.branchBase_domain (c i) (LinearContactSquareclass318.contacts i)
  apply isIntegrallyClosed_of_isLocalization (OpenBase c i)
    (Submonoid.powers (FiniteBranchChart318.denominator (c i)
      (LinearContactSquareclass318.contacts i) (otherTwist c i) (otherContact i)))
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n
    (FiniteBranchChart318.denominator_ne_zero _ _ _ _ (other_distinct i)))

/-- The entire finite-branch order is normal, not a selected component. -/
lemma chart_integrallyClosed : IsIntegrallyClosed (OpenOrder c i) := by
  letI:=openBase_integrallyClosed c i
  letI:=FiniteBranchChart318.openBase_domain (c i) (LinearContactSquareclass318.contacts i)
    (otherTwist c i) (otherContact i) (other_distinct i)
  letI:=source_chart_domain c i
  letI:Module.Finite (OpenBase c i) (OpenOrder c i):=(source_finite_branch c i).1
  letI:Algebra.Etale (OpenBase c i) (OpenOrder c i):=(source_finite_branch c i).2.2.1
  exact SmoothGenericField318.smooth_integrallyClosed
    (R:=OpenBase c i) (K:=FractionRing (OpenBase c i)) (B:=OpenOrder c i)

lemma localized_integrallyClosed :
    IsIntegrallyClosed (Localization.Away (SourceDenominatorCover318.denominator c i)) := by
  letI:=chart_integrallyClosed c i
  exact IsIntegrallyClosed.of_equiv
    (SourceBranchLocalization318.sourceLocalizationEquiv c i).symm.toRingEquiv

end SourceBranchNormal318
