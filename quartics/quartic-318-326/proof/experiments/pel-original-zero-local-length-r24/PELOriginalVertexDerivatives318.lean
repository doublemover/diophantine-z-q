module
public import PELOriginalProjectiveTangents318
public import PELDirichletIncidence318
public section
noncomputable section
namespace PELOriginalVertexDerivatives318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318
open PELDirichletVertexCycles318 PELDirichletVertexFan318
open PELOriginalProjectiveTangents318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def inversePrefix (v : Fin 28) : B :=
  embed (conjugateCoordinates (prefixCoordinates v))

theorem inversePrefix_norm (v : Fin 28) : reducedNorm (inversePrefix v)=1 := by
  fin_cases v <;> norm_num [inversePrefix,prefixCoordinates,conjugateCoordinates,embed,reducedNorm]

theorem real_denominator_positive (v : Fin 28) :
    0<PELRealProjectiveDifferential318.denominator
      (realMatrix (inversePrefix v)) (realPoint (vertex v)) := by
  rw [denominator_cast]
  exact_mod_cast inverse_denominator_positive v

/-- The displayed rational fan is now evaluated by the ACTUAL real
Frechet derivative of the same original accumulated inverse-unit action. -/
theorem actual_tangent_ray (v : Fin 28) :
    PELRealProjectiveDifferential318.differential
      (realMatrix (inversePrefix v)) (realPoint (vertex v)) (realPoint (sideDirection v))=
      (rayScale v:ℝ) • realPoint (ray v) := by
  rw [differential_cast _ _ _ (inverse_denominator_positive v).ne']
  change realPoint (tangentFormula (embed (conjugateCoordinates (prefixCoordinates v)))
    (vertex v) (sideDirection v))=_
  rw [original_tangent_ray]
  apply Prod.ext <;> simp [realPoint]

theorem actual_fan_derivative (v : Fin 28) :
    HasFDerivAt (PELRealProjectiveDifferential318.realAction (realMatrix (inversePrefix v)))
      (PELRealProjectiveDifferential318.differential
        (realMatrix (inversePrefix v)) (realPoint (vertex v))) (realPoint (vertex v)) :=
  PELRealProjectiveDifferential318.hasFDerivAt_realAction _ _ (real_denominator_positive v).ne'

theorem actual_fan_orientation (v : Fin 28) :
    0<(PELRealProjectiveDifferential318.jacobian
      (realMatrix (inversePrefix v)) (realPoint (vertex v))).det := by
  apply actual_orientation _ _ _ (real_denominator_positive v)
  rw [inversePrefix_norm]
  norm_num

theorem actual_fan_invertible (v : Fin 28) :
    Function.Bijective (PELRealProjectiveDifferential318.differential
      (realMatrix (inversePrefix v)) (realPoint (vertex v))) := by
  apply actual_differential_bijective _ _ _ (real_denominator_positive v).ne'
  intro hz
  have hn := inversePrefix_norm v
  rw [hz] at hn
  norm_num [reducedNorm] at hn

theorem original_cycle_real_matrix (i : Fin 5) :
    realMatrix (originalWord (cycleWord i))=1 := by
  change (PELQuaternionKleinAction318.matrix (originalWord (cycleWord i))).map
    (algebraMap ℚ ℝ)=1
  rw [cycle_homogeneous_identity]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num

theorem identity_action (P : ℝ × ℝ) : PELRealProjectiveDifferential318.realAction 1 P=P := by
  apply Prod.ext <;>
    simp [PELRealProjectiveDifferential318.realAction,PELRealProjectiveDifferential318.denominator]

/-- The original signed cycle product acts identically on EVERY real
projective chart point, not only the finite list of vertices. The local
polygon quotient theorem is still needed to turn the fan into a disk chart. -/
theorem original_cycle_return (i : Fin 5) (P : ℝ × ℝ) :
    PELRealProjectiveDifferential318.realAction (realMatrix (originalWord (cycleWord i))) P=P := by
  rw [original_cycle_real_matrix]
  exact identity_action P
end PELOriginalVertexDerivatives318
