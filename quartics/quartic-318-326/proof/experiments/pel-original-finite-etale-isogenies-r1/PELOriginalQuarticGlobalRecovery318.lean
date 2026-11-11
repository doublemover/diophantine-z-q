module
public import PELOriginalQuarticGlobalSections318
public import PELOriginalWholePowerGlobalRecovery318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public section
noncomputable section
namespace PELOriginalQuarticGlobalRecovery318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalSectionMultiplication318 PELOriginalQuarticMixedCoefficients318
open PELOriginalQuarticGlobalSections318
open PELOriginalLevelPowerSections318 PELOriginalPowerSectionLift318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Recover the WHOLE chart coefficient from the constructed global
section by the actual inverse frame and actual original-open ring iso. -/
theorem coefficient_recovery (s : homogeneous τ hτ 4) (a : NonemptyIndex τ hτ) :
    (LineFrameTopScalar318.ringTop (opens τ hτ a)).inv
      ((OpenLineFrameCoordinates318.frame (Power τ hτ) (opens τ hτ a)
        (frame τ hτ a) (opens τ hτ a) le_rfl).symm
          ((Power τ hτ).presheaf.map
            (homOfLE (show opens τ hτ a ≤ ⊤ from le_top)).op (global τ hτ s)))=
      regular τ hτ a.val s := by
  rw [global_restrict,LinearEquiv.symm_apply_apply,coefficient]
  exact Iso.hom_inv_id_apply _ _

/-- The actual recovered local coefficient evaluates to the original
entire representative divided by its SAME quadratic coordinate squared. -/
theorem recovered_evaluation (s : homogeneous τ hτ 4) (a : NonemptyIndex τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a).toScheme)
    (z : ComplexVectors) (h3 : value τ hτ 3 a.val.1 z≠0) (h2 : value τ hτ 2 a.val.2 z≠0)
    (hp : p ≫ (opens τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop (opens τ hτ a)).inv
        ((OpenLineFrameCoordinates318.frame (Power τ hτ) (opens τ hτ a)
          (frame τ hτ a) (opens τ hτ a) le_rfl).symm
            ((Power τ hτ).presheaf.map
              (homOfLE (show opens τ hτ a ≤ ⊤ from le_top)).op (global τ hτ s)))))=
        lift τ hτ 4 (PELOriginalWholeHZeroDimension318.asSection τ hτ 4 s) z /
          (value τ hτ 2 a.val.2 z)^2 := by
  rw [coefficient_recovery]
  exact regular_evaluation τ hτ a.val s p z h3 h2 hp

/-- Algebraization is faithful on the FULL original H0(4). Its proof
uses real mixed-chart points and the nonzero original bundle gauge. -/
theorem global_injective : Function.Injective (global τ hτ) := by
  intro s t hst
  apply Subtype.ext
  funext q
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  obtain ⟨a,p,hp⟩ := PELOriginalWholePowerGlobalRecovery318.exists_mixed_point τ hτ (projection (P τ) z)
  obtain ⟨hz,h2⟩ := PELOriginalMixedPointEvaluation318.coordinates_nonzero τ hτ a.val p z hp
  have hc : regular τ hτ a.val s=regular τ hτ a.val t := by
    rw [←coefficient_recovery τ hτ s a,←coefficient_recovery τ hτ t a,hst]
  have he := congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop c)) hc
  rw [regular_evaluation τ hτ a.val s p z hz h2 hp,regular_evaluation τ hτ a.val t p z hz h2 hp] at he
  change lift τ hτ 4 (PELOriginalWholeHZeroDimension318.asSection τ hτ 4 s) z /
    (value τ hτ 2 a.val.2 z)^2 =
    lift τ hτ 4 (PELOriginalWholeHZeroDimension318.asSection τ hτ 4 t) z /
      (value τ hτ 2 a.val.2 z)^2 at he
  have hl := (div_left_inj (pow_ne_zero 2 h2)).mp he
  change (gauge τ hτ 4 z)⁻¹*s.val (projection (P τ) z)=
    (gauge τ hτ 4 z)⁻¹*t.val (projection (P τ) z) at hl
  exact mul_left_cancel₀ (inv_ne_zero (gauge_ne_zero τ hτ 4 z)) hl
end PELOriginalQuarticGlobalRecovery318
