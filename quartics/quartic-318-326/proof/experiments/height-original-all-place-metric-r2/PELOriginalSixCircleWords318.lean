module
public import PELOriginalCircleWordMatrices318
public section
noncomputable section
namespace PELOriginalSixCircleWords318
open PELOriginalCircleWordMatrices318 PELQuaternionRealRepresentation318
open PELPositiveNormalizerMobius318 PELPositiveOrderNormalizer318
open PELFixedCandidateConjugators318 PELFixedCandidateWords318
open PELActualSixGeodesicCharts318 QuaternionicMobiusPeriods318

lemma alpha_cube : alpha^3=210*alpha := by
  calc alpha^3=alpha*alpha^2:=by ring
       _=210*alpha:=by rw [alpha_sq];ring
lemma beta_cube : beta^3=5*beta := by
  calc beta^3=beta*beta^2:=by ring
       _=5*beta:=by rw [beta_sq];ring
lemma alpha_fourth : alpha^4=44100 := by
  calc alpha^4=(alpha^2)^2:=by ring
       _=44100:=by rw [alpha_sq];norm_num
lemma beta_fourth : beta^4=25 := by
  calc beta^4=(beta^2)^2:=by ring
       _=25:=by rw [beta_sq];norm_num

/-- Identify the inverse of the SAME original group element using its
actual representation and matrix multiplication, not a projective guess. -/
lemma original_inverse_matrix (g:positiveNormalizer)
    (N:Matrix (Fin 2) (Fin 2) ℝ)
    (hN:N*PELPositiveNormalizerMobius318.matrix g=1) :
    PELPositiveNormalizerMobius318.matrix (g⁻¹)=N := by
  have hr:PELPositiveNormalizerMobius318.matrix g*
      PELPositiveNormalizerMobius318.matrix (g⁻¹)=1:=by
    rw [←PELPositiveNormalizerMobius318.matrix_mul,mul_inv_cancel,
      PELPositiveNormalizerMobius318.matrix_one]
  calc
    PELPositiveNormalizerMobius318.matrix (g⁻¹)=1*PELPositiveNormalizerMobius318.matrix (g⁻¹):=by simp
    _=(N*PELPositiveNormalizerMobius318.matrix g)*PELPositiveNormalizerMobius318.matrix (g⁻¹):=by rw [hN]
    _=N*(PELPositiveNormalizerMobius318.matrix g*PELPositiveNormalizerMobius318.matrix (g⁻¹)):=mul_assoc _ _ _
    _=N:=by rw [hr,mul_one]

lemma left_vertical_matrix : PELPositiveNormalizerMobius318.matrix ((conjugator 18)⁻¹)=
    (-alpha*beta/1050) • circleMatrix 3 := by
  apply original_inverse_matrix
  rw [vertical_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [circleMatrix,middle,leading,constantTerm,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.smul_apply,Matrix.one_apply] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq,alpha_cube,beta_cube,alpha_fourth,beta_fourth] <;> ring

lemma left_slant_matrix : PELPositiveNormalizerMobius318.matrix ((conjugator 23)⁻¹)=
    (alpha*beta/1050) • circleMatrix 5 := by
  apply original_inverse_matrix
  rw [slant_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [circleMatrix,middle,leading,constantTerm,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.smul_apply,Matrix.one_apply] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq,alpha_cube,beta_cube,alpha_fourth,beta_fourth] <;> ring

@[expose] def sixSideWord : Fin 6→positiveNormalizer :=
  ![inertiaElement 4,inertiaElement 1,conjugator 18,(conjugator 18)⁻¹,
    conjugator 23,(conjugator 23)⁻¹]
@[expose] def sixSideScale : Fin 6→ℝ :=
  ![alpha,alpha*beta/10,alpha*beta/150,-alpha*beta/1050,
    -alpha*beta/70,alpha*beta/1050]

theorem original_six_matrix (i:Fin 6) :
    PELPositiveNormalizerMobius318.matrix (sixSideWord i)=sixSideScale i • circleMatrix i := by
  fin_cases i
  · exact center_matrix
  · exact top_matrix
  · exact vertical_matrix
  · exact left_vertical_matrix
  · exact slant_matrix
  · exact left_slant_matrix

lemma sixSideScale_ne_zero (i:Fin 6) : sixSideScale i≠0 := by
  have ha:=alpha_pos.ne'
  have hb:=beta_pos.ne'
  fin_cases i <;> simp [sixSideScale,ha,hb]

/-- ALL SIX genuine original side words act by the exact circle/mirror
formula on the whole upper half-plane. Left sides use actual inverse
chronological words, with proved inverse matrices and retained scalars. -/
theorem original_six_action (i:Fin 6) (τ:QuaternionicJointPeriodTopology318.HalfPlane) :
    (baseAction (sixSideWord i) τ:ℂ)=
      ((-(middle i:ℂ))*τ+(constantTerm i:ℂ))/((leading i:ℂ)*τ-(middle i:ℂ)) := by
  change mobius (PELPositiveNormalizerMobius318.matrix (sixSideWord i)) τ=_
  rw [original_six_matrix,mobius_smul _ (sixSideScale_ne_zero i)]
  simp [mobius,denominator,circleMatrix,sub_eq_add_neg]
end PELOriginalSixCircleWords318
