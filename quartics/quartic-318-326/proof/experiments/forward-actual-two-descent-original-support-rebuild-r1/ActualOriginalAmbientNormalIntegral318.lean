module
public import ActualOriginalWholeNormalSubstitution318
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public section
noncomputable section
namespace ActualOriginalAmbientNormalIntegral318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalNormalJacobian318
open ActualOriginalJointLevelDensity318 ActualOriginalNormalProfile318
open ActualOriginalWholeNormalSubstitution318 MeasureTheory
set_option maxHeartbeats 16000000

/-- Reassociation is a genuine volume-preserving measurable equivalence,
not a Jacobian assertion about a nonlinear coordinate map. -/
lemma actual_original_volume_regroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Coordinates ℝ→E) :
    (∫x : Coordinates ℝ,F x)=∫z : ℝ×Parameters,F (assemble z.1 z.2) := by
  exact volume_preserving_prodAssoc.integral_comp' (fun z : ℝ×Parameters => F (assemble z.1 z.2))

lemma actual_regrouped_compact {E : Type*} [Zero E]
    (F : Coordinates ℝ→E) (hF : HasCompactSupport F) :
    HasCompactSupport (fun z : ℝ×Parameters => F (assemble z.1 z.2)) := by
  exact hF.comp_homeomorph (Homeomorph.prodAssoc ℝ ℝ ((ℝ×ℝ)×ℝ)).symm

/-- Actual original ambient-volume change of variables. Fubini is used
only after integrability of both compact continuous weighted integrands
has been produced. Arbitrary continuous vector-valued phases remain exact. -/
theorem actual_original_ambient_normal_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0)
    (phase : ℝ→E) (hphase : Continuous phase) :
    (∫x : Coordinates ℝ,W x • phase (equation κ x))=
      ∫s : ℝ,normalProfile κ W s • phase s := by
  let F : Coordinates ℝ→E := fun x => W x • phase (equation κ x)
  let D : ℝ×Parameters→E := fun z => levelDensity κ W z • phase z.1
  have hFc : HasCompactSupport F := by
    apply hWc.mono
    intro x hx hwzero
    exact hx (by simp only [F,hwzero,zero_smul])
  have hFcont : Continuous F := hW.smul
    (hphase.comp (ActualOriginalRealGoodRegion318.original_equation_continuous κ))
  have hRegCont : Continuous (fun z : ℝ×Parameters => F (assemble z.1 z.2)) := by
    apply hFcont.comp
    unfold assemble
    fun_prop
  have hRegInt : Integrable (fun z : ℝ×Parameters => F (assemble z.1 z.2)) :=
    hRegCont.integrable_of_hasCompactSupport (actual_regrouped_compact F hFc)
  have hDc : HasCompactSupport D := by
    apply (level_density_compact κ η hη W hWc hb).mono
    intro z hz hzero
    exact hz (by simp only [D,hzero,zero_smul])
  have hDcont : Continuous D :=
    (level_density_continuous κ η hη W hW hb).smul (hphase.comp continuous_fst)
  have hDInt : Integrable D := hDcont.integrable_of_hasCompactSupport hDc
  calc
    _ = ∫z : ℝ×Parameters,F (assemble z.1 z.2) := actual_original_volume_regroup F
    _ = ∫v : Parameters,∫a : ℝ,F (assemble a v) :=
      integral_prod_symm (fun z : ℝ×Parameters => F (assemble z.1 z.2)) hRegInt
    _ = ∫v : Parameters,∫s : ℝ,D (s,v) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v =>
        actual_original_whole_normal_substitution κ η hη W hW hWc hb phase hphase v)
    _ = ∫z : ℝ×Parameters,D z := (integral_prod_symm D hDInt).symm
    _ = ∫s : ℝ,∫v : Parameters,D (s,v) := integral_prod D hDInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      exact integral_smul_const (fun v : Parameters => levelDensity κ W (s,v)) (phase s)

end ActualOriginalAmbientNormalIntegral318
