module
public import PELMaximalHalfOctagonBoundaryAction318
public import PELActualSixGeodesicCharts318
public section
noncomputable section
namespace PELOriginalCircleWordMatrices318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELQuaternionRealRepresentation318 PELPositiveOrderNormalizer318
open PELPositiveNormalizerMobius318 PELFixedCandidateConjugators318 PELFixedCandidateWords318
open PELMaximalHalfOctagonBoundaryAction318 PELActualSixGeodesicCharts318
open QuaternionicMobiusPeriods318

/-- The actual holomorphic matrix obtained by composing the fixed mirror
with reflection in the original geodesic circle. -/
@[expose] def circleMatrix (i:Fin 6) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-middle i,constantTerm i;leading i,-middle i]

/-- Exact chronological words, without replacing a word by a convenient
projectively equal quaternion. The negative scalar of word 18 is retained. -/
@[expose] def sideWord : Fin 4→positiveNormalizer :=
  ![inertiaElement 4,inertiaElement 1,conjugator 18,conjugator 23]
@[expose] def sideIndex : Fin 4→Fin 6 := ![0,1,2,4]
@[expose] def sideScale : Fin 4→ℝ :=
  ![alpha,alpha*beta/10,alpha*beta/150,-alpha*beta/70]

theorem center_matrix : PELPositiveNormalizerMobius318.matrix (inertiaElement 4)=
    alpha • circleMatrix 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [PELPositiveNormalizerMobius318.matrix,inertiaElement,
      PELInertiaNormalizerData318.rationalUnit,PELInertiaNormalizerData318.element,
      PELInertiaNormalizerData318.coefficients,representation,
      PELQuaternionRealRepresentation318.matrix,embed,circleMatrix,middle,
      leading,constantTerm,Matrix.smul_apply]

theorem top_matrix : PELPositiveNormalizerMobius318.matrix (inertiaElement 1)=
    (alpha*beta/10) • circleMatrix 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [PELPositiveNormalizerMobius318.matrix,inertiaElement,
      PELInertiaNormalizerData318.rationalUnit,PELInertiaNormalizerData318.element,
      PELInertiaNormalizerData318.coefficients,representation,
      PELQuaternionRealRepresentation318.matrix,embed,circleMatrix,middle,
      leading,constantTerm,Matrix.smul_apply] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

theorem vertical_matrix : PELPositiveNormalizerMobius318.matrix (conjugator 18)=
    (alpha*beta/150) • circleMatrix 2 := by
  unfold PELPositiveNormalizerMobius318.matrix
  rw [vertical_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [representation,PELQuaternionRealRepresentation318.matrix,embed,
      circleMatrix,middle,leading,constantTerm,Matrix.smul_apply] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

theorem slant_matrix : PELPositiveNormalizerMobius318.matrix (conjugator 23)=
    (-alpha*beta/70) • circleMatrix 4 := by
  unfold PELPositiveNormalizerMobius318.matrix
  rw [slant_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [representation,PELQuaternionRealRepresentation318.matrix,embed,
      circleMatrix,middle,leading,constantTerm,Matrix.smul_apply] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

theorem original_side_matrix (k:Fin 4) :
    PELPositiveNormalizerMobius318.matrix (sideWord k)=
      sideScale k • circleMatrix (sideIndex k) := by
  fin_cases k
  · exact center_matrix
  · exact top_matrix
  · exact vertical_matrix
  · exact slant_matrix

theorem sideScale_ne_zero (k:Fin 4) : sideScale k≠0 := by
  have ha:=alpha_pos.ne'
  have hb:=beta_pos.ne'
  fin_cases k <;> simp [sideScale,ha,hb]

/-- Scalar cancellation is valid for the entire Mobius rational function,
including its totalized value at a denominator zero. No circle equation or
rationality restriction is present. -/
theorem mobius_smul (c:ℝ) (hc:c≠0) (M:Matrix (Fin 2) (Fin 2) ℝ) (z:ℂ) :
    mobius (c • M) z=mobius M z := by
  have hc':(c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc
  simp only [mobius,denominator,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul]
  rw [show (c:ℂ)*(M 0 0:ℂ)*z+(c:ℂ)*(M 0 1:ℂ)=
    (c:ℂ)*((M 0 0:ℂ)*z+(M 0 1:ℂ)) by ring,
    show (c:ℂ)*(M 1 0:ℂ)*z+(c:ℂ)*(M 1 1:ℂ)=
    (c:ℂ)*((M 1 0:ℂ)*z+(M 1 1:ℂ)) by ring]
  exact mul_div_mul_left _ _ hc'

/-- The exact original normalizer acts by the circle/mirror formula on
EVERY original upper-half-plane point, not only on a boundary side. -/
theorem original_side_action (k:Fin 4) (τ:QuaternionicJointPeriodTopology318.HalfPlane) :
    (baseAction (sideWord k) τ:ℂ)=
      ((-(middle (sideIndex k):ℂ))*τ+(constantTerm (sideIndex k):ℂ))/
        ((leading (sideIndex k):ℂ)*τ-(middle (sideIndex k):ℂ)) := by
  change mobius (PELPositiveNormalizerMobius318.matrix (sideWord k)) τ=_
  rw [original_side_matrix,mobius_smul _ (sideScale_ne_zero k)]
  simp [mobius,denominator,circleMatrix,sub_eq_add_neg]
end PELOriginalCircleWordMatrices318
