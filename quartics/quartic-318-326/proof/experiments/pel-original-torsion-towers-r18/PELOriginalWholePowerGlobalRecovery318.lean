module
public import PELOriginalWholePowerGlobalSections318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public section
noncomputable section
namespace PELOriginalWholePowerGlobalRecovery318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalSectionMultiplication318 PELOriginalWholePowerMixedCoefficient318
open PELOriginalWholePowerMixedTransition318 PELOriginalWholePowerGlobalSections318
open PELOriginalLevelPowerSections318 PELOriginalPowerSectionLift318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Every original point lifts through a genuine mixed OPEN IMMERSION;
this is a whole Spec(C)-morphism equality, not merely a point equality. -/
theorem exists_mixed_point (q : PELOriginalPolarizationTransitions318.Base τ) :
    ∃ a : NonemptyIndex τ hτ,
      ∃ p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a).toScheme,
        p ≫ (opens τ hτ a).ι=candidateComplexPoint τ hτ q := by
  let f := candidateComplexPoint τ hτ q
  let o : Spec (CommRingCat.of ℂ) := IsLocalRing.closedPoint ℂ
  obtain ⟨a,ha⟩ := nonempty_covers τ hτ (f o)
  have hr : Set.range f ⊆ Set.range (opens τ hτ a).ι := by
    rintro _ ⟨y,rfl⟩
    have hy : y=o := Subsingleton.elim _ _
    subst y
    exact ⟨⟨f o,ha⟩,rfl⟩
  exact ⟨a,IsOpenImmersion.lift (opens τ hτ a).ι f hr,
    IsOpenImmersion.lift_fac _ _ hr⟩

variable (m : ℕ)
/-- Recover the WHOLE chart coefficient from the constructed global
section by the actual inverse frame and actual original-open ring iso. -/
theorem coefficient_recovery (s : homogeneous τ hτ (3*m)) (a : NonemptyIndex τ hτ) :
    (LineFrameTopScalar318.ringTop (opens τ hτ a)).inv
      ((OpenLineFrameCoordinates318.frame (power τ hτ m) (opens τ hτ a)
        (frame τ hτ m a) (opens τ hτ a) le_rfl).symm
          ((power τ hτ m).presheaf.map
            (homOfLE (show opens τ hτ a ≤ ⊤ from le_top)).op (global τ hτ m s)))=
      coefficient τ hτ m a.val s := by
  rw [global_restrict,LinearEquiv.symm_apply_apply,originalCoefficient]
  exact Iso.hom_inv_id_apply _ _

/-- The actual recovered local coefficient evaluates to the original
entire representative divided by its SAME cubic coordinate power. -/
theorem recovered_evaluation (s : homogeneous τ hτ (3*m)) (a : NonemptyIndex τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a).toScheme)
    (z : ComplexVectors) (hz : value τ hτ 3 a.val.1 z≠0)
    (hp : p ≫ (opens τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop (opens τ hτ a)).inv
        ((OpenLineFrameCoordinates318.frame (power τ hτ m) (opens τ hτ a)
          (frame τ hτ m a) (opens τ hτ a) le_rfl).symm
            ((power τ hτ m).presheaf.map
              (homOfLE (show opens τ hτ a ≤ ⊤ from le_top)).op (global τ hτ m s)))))=
        PELOriginalWholePowerRatioCover318.coverRatio τ hτ m a.val.1 s z := by
  rw [coefficient_recovery]
  exact evaluation τ hτ m a.val s p z hz hp

/-- Algebraization is faithful on the FULL original H0(3m). Its proof
uses real mixed-chart points and the nonzero original bundle gauge. -/
theorem global_injective : Function.Injective (global τ hτ m) := by
  intro s t hst
  apply Subtype.ext
  funext q
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  obtain ⟨a,p,hp⟩ := exists_mixed_point τ hτ (projection (P τ) z)
  obtain ⟨hz,h2⟩ := PELOriginalMixedPointEvaluation318.coordinates_nonzero τ hτ a.val p z hp
  have hc : coefficient τ hτ m a.val s=coefficient τ hτ m a.val t := by
    rw [←coefficient_recovery τ hτ m s a,←coefficient_recovery τ hτ m t a,hst]
  have he := congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop c)) hc
  rw [evaluation τ hτ m a.val s p z hz hp,evaluation τ hτ m a.val t p z hz hp] at he
  change lift τ hτ (3*m) (PELOriginalWholeHZeroDimension318.asSection τ hτ (3*m) s) z /
    (value τ hτ 3 a.val.1 z)^m =
    lift τ hτ (3*m) (PELOriginalWholeHZeroDimension318.asSection τ hτ (3*m) t) z /
      (value τ hτ 3 a.val.1 z)^m at he
  have hl := (div_left_inj (pow_ne_zero m hz)).mp he
  change (gauge τ hτ (3*m) z)⁻¹*s.val (projection (P τ) z)=
    (gauge τ hτ (3*m) z)⁻¹*t.val (projection (P τ) z) at hl
  exact mul_left_cancel₀ (inv_ne_zero (gauge_ne_zero τ hτ (3*m) z)) hl
end PELOriginalWholePowerGlobalRecovery318
