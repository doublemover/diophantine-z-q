module
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public section
noncomputable section
namespace JacobianLocalSmooth318
open Algebra
set_option maxHeartbeats 0
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Localizing an actual finite presentation at its chosen Jacobian minor
makes that same presentation genuinely standard smooth. -/
theorem localization_jacobian {ι σ : Type} [Finite ι] [Finite σ]
    (P : PreSubmersivePresentation R S ι σ) :
    IsStandardSmooth R (Localization.Away P.jacobian) := by
  let T := Localization.Away P.jacobian
  let Q : PreSubmersivePresentation S T Unit Unit :=
    PreSubmersivePresentation.localizationAway T P.jacobian
  let E : SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { toPreSubmersivePresentation := Q.comp P
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        have hu := IsLocalization.Away.algebraMap_isUnit (S := T) P.jacobian
        apply hu.mul
        change IsUnit (PreSubmersivePresentation.localizationAway T P.jacobian).jacobian
        rw [PreSubmersivePresentation.localizationAway_jacobian]
        exact hu }
  exact E.isStandardSmooth

end JacobianLocalSmooth318
