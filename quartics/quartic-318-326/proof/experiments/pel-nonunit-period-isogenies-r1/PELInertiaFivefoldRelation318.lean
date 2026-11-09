module
public import PELInertiaPrimeWord318
public section
noncomputable section
namespace PELInertiaFivefoldRelation318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELInertiaNormalizerData318 PELInertiaPrimeWord318
set_option maxHeartbeats 1400000

/-- The exact residual integral unit in the full five-inertia product. -/
@[expose] def residualUnit : orderˣ where
  val := coordinatesEquiv ![13,-2,13,4]
  inv := coordinatesEquiv ![26,2,-13,-4]
  val_inv := by
    apply Subtype.ext
    change embed ![13,-2,13,4]*embed ![26,2,-13,-4]=1
    ext <;> norm_num [embed]
  inv_val := by
    apply Subtype.ext
    change embed ![26,2,-13,-4]*embed ![13,-2,13,4]=1
    ext <;> norm_num [embed]

theorem residualUnit_norm : reducedNorm ((residualUnit:order):B)=1 := by
  change reducedNorm (embed ![13,-2,13,4])=1
  norm_num [embed,reducedNorm]

/-- The original five representatives satisfy the full relation modulo a
specified positive rational scalar and a specified norm-one ORIGINAL unit.
This is not an assertion that their raw quaternion product is the identity. -/
theorem fivefold_relation :
    element 0*element 1*element 2*element 3*element 4=
      (44100:ℚ) • ((residualUnit:order):B) := by
  change element 0*element 1*element 2*element 3*element 4=
    (44100:ℚ) • embed ![13,-2,13,4]
  ext <;> norm_num [element,coefficients,embed]

/-- Every original prime occurs four times in the full five-label product;
the retained scalar is exactly210². -/
theorem fivefold_scalar : (44100:ℚ)=210^2 := by norm_num

/-- A compact connected consumer retains the label, actual word, actual
fixed point and actual full fivefold relation in the same algebra. -/
theorem original_inertia_realization (i : Fin 5) :
    reducedNorm (element i)=InertiaLabels318.divisor (InertiaLabels318.fiveLabels i) ∧
    element i*element i=algebraMap ℚ B (-(discriminant i:ℚ)) ∧
    element i=((connectingUnit i:order):B)*(word (InertiaLabels318.fiveLabels i):B) ∧
    0<(PELInertiaRealFixedPoints318.fixedPoint i).im := by
  rw [label_identity]
  exact ⟨element_norm i,element_square i,original_label_word i,
    PELInertiaRealFixedPoints318.fixedPoint_im_positive i⟩
end PELInertiaFivefoldRelation318
