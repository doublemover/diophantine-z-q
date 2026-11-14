module
public import PELPrimeOrderConjugation318
public section
noncomputable section
namespace PELPrimeNormalizerRelations318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318
set_option maxHeartbeats 1800000
@[expose] def squareCoefficients : Fin 4 → Coordinates := ![![47,16,32,-24],![29,10,15,-15],![1,0,1,0],![20,15,21,-21]]
@[expose] def squareInverseCoefficients : Fin 4 → Coordinates := ![![79,-16,-32,24],![44,-10,-15,15],![2,0,-1,0],![41,-15,-21,21]]
@[expose] def commutatorCoefficients : Fin 4 → Fin 4 → Coordinates := ![![![1,0,0,0],![92,123,-217,-165],![-20,-19,21,26],![817,703,-717,-965]],![![-125,-123,217,165],![1,0,0,0],![-13,-11,14,15],![407,299,-342,-410]],![![1,19,-21,-26],![1,11,-14,-15],![1,0,0,0],![1,21,-6,-29]],![![100,-703,717,965],![65,-299,342,410],![-5,-21,6,29],![1,0,0,0]]]

/-- The actual square divided by its prime is an ORIGINAL integral unit. -/
@[expose] def squareUnit (i : Fin 4) : orderˣ where
  val := coordinatesEquiv (squareCoefficients i)
  inv := coordinatesEquiv (squareInverseCoefficients i)
  val_inv := by
    apply Subtype.ext
    change embed (squareCoefficients i)*embed (squareInverseCoefficients i)=1
    fin_cases i <;> ext <;> norm_num [squareCoefficients,squareInverseCoefficients,embed]
  inv_val := by
    apply Subtype.ext
    change embed (squareInverseCoefficients i)*embed (squareCoefficients i)=1
    fin_cases i <;> ext <;> norm_num [squareCoefficients,squareInverseCoefficients,embed]

theorem squareUnit_norm (i : Fin 4) : reducedNorm ((squareUnit i:order):B)=1 := by
  change reducedNorm (embed (squareCoefficients i))=1
  fin_cases i <;> norm_num [squareCoefficients,embed,reducedNorm]

theorem square_relation (i : Fin 4) :
    element i^2=(prime i:ℚ) • ((squareUnit i:order):B) := by
  change element i^2=(prime i:ℚ) • embed (squareCoefficients i)
  fin_cases i <;> ext <;> norm_num [element,coefficients,prime,squareCoefficients,embed,pow_two]

/-- All16 commutators lie in the SAME norm-one integral unit group.
The inverse is the actual reverse commutator, not a postulated unit. -/
@[expose] def commutatorUnit (i j : Fin 4) : orderˣ where
  val := coordinatesEquiv (commutatorCoefficients i j)
  inv := coordinatesEquiv (commutatorCoefficients j i)
  val_inv := by
    apply Subtype.ext
    change embed (commutatorCoefficients i j)*embed (commutatorCoefficients j i)=1
    fin_cases i <;> fin_cases j <;> ext <;> norm_num [commutatorCoefficients,embed]
  inv_val := by
    apply Subtype.ext
    change embed (commutatorCoefficients j i)*embed (commutatorCoefficients i j)=1
    fin_cases i <;> fin_cases j <;> ext <;> norm_num [commutatorCoefficients,embed]

theorem commutatorUnit_norm (i j : Fin 4) :
    reducedNorm ((commutatorUnit i j:order):B)=1 := by
  change reducedNorm (embed (commutatorCoefficients i j))=1
  fin_cases i <;> fin_cases j <;> norm_num [commutatorCoefficients,embed,reducedNorm]

/-- Pairwise commutation modulo actual norm-one order units is an equality
of original rational quaternions. It does not presume a deck-group quotient. -/
theorem commutator_relation (i j : Fin 4) :
    element i*element j=((commutatorUnit i j:order):B)*(element j*element i) := by
  change element i*element j=embed (commutatorCoefficients i j)*(element j*element i)
  fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [commutatorCoefficients,element,coefficients,embed]
end PELPrimeNormalizerRelations318
