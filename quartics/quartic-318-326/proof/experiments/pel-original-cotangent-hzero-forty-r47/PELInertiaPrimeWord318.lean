module
public import PELInertiaRealFixedPoints318
public section
noncomputable section
namespace PELInertiaPrimeWord318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELInertiaNormalizerData318
set_option maxHeartbeats 1800000
/-- The actual ordered word in the four specified original rational units.
Its support is the original four-coordinate inertia label. -/
@[expose] def word (v : InertiaLabels318.V) : Bˣ :=
  (if v 0=0 then 1 else PELPrimeNormalizerData318.rationalUnit 0)*
  (if v 1=0 then 1 else PELPrimeNormalizerData318.rationalUnit 1)*
  (if v 2=0 then 1 else PELPrimeNormalizerData318.rationalUnit 2)*
  (if v 3=0 then 1 else PELPrimeNormalizerData318.rationalUnit 3)

@[expose] def unitCoefficients : Fin 5 → Coordinates :=
  ![![191,-73,-39,105],![-547,-91,447,110],![-169,34,69,-51],
    ![-89,20,31,-30],![1429,76,-987,-66]]
@[expose] def inverseCoefficients : Fin 5 → Coordinates :=
  ![![152,73,39,-105],![-100,91,-447,-110],![-100,-34,-69,51],
    ![-58,-20,-31,30],![442,-76,987,66]]

/-- These are constructed original integral units, not inferred from equality
of reduced norms or squareclasses. -/
@[expose] def connectingUnit (i : Fin 5) : orderˣ where
  val := coordinatesEquiv (unitCoefficients i)
  inv := coordinatesEquiv (inverseCoefficients i)
  val_inv := by
    apply Subtype.ext
    change embed (unitCoefficients i)*embed (inverseCoefficients i)=1
    fin_cases i <;> ext <;> norm_num [unitCoefficients,inverseCoefficients,embed]
  inv_val := by
    apply Subtype.ext
    change embed (inverseCoefficients i)*embed (unitCoefficients i)=1
    fin_cases i <;> ext <;> norm_num [unitCoefficients,inverseCoefficients,embed]

theorem connectingUnit_norm (i : Fin 5) : reducedNorm ((connectingUnit i:order):B)=1 := by
  change reducedNorm (embed (unitCoefficients i))=1
  fin_cases i <;> norm_num [unitCoefficients,embed,reducedNorm]

/-- The FIVE fixed-point normalizers really represent the original FOUR
prime-label words modulo explicitly constructed original norm-one units. -/
theorem original_label_word (i : Fin 5) :
    element i=((connectingUnit i:order):B)*
      (word (InertiaLabels318.fiveLabels i):B) := by
  change element i=embed (unitCoefficients i)*(word (InertiaLabels318.fiveLabels i):B)
  fin_cases i <;> ext <;>
    norm_num [element,coefficients,unitCoefficients,word,
      InertiaLabels318.fiveLabels,InertiaLabels318.labels,
      PELPrimeNormalizerData318.rationalUnit,PELPrimeNormalizerData318.element,
      PELPrimeNormalizerData318.coefficients,embed]

/-- The word has the exact literal label norm, not an unspecified
representative of that norm squareclass. -/
theorem original_word_norm (i : Fin 5) :
    reducedNorm (word (InertiaLabels318.fiveLabels i):B)=discriminant i := by
  fin_cases i <;>
    norm_num [word,InertiaLabels318.fiveLabels,InertiaLabels318.labels,
      PELPrimeNormalizerData318.rationalUnit,PELPrimeNormalizerData318.element,
      PELPrimeNormalizerData318.coefficients,embed,reducedNorm,discriminant]
end PELInertiaPrimeWord318
