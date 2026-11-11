module
public import PELMaximalComplexAtlas318
public import PELQuaternionDivision318
public import PELDirichletPolygonCertificate318
public section
noncomputable section
namespace PELDirichletOriginalUnits318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELQuaternionAnisotropy318
open PELQuaternionDivision318 PELJointNormOneAction318
set_option maxHeartbeats 1800000

@[expose] def integerNorm (a : Coordinates) : ℤ :=
  a 0^2+a 0*a 2+210*a 1^2+210*a 1*a 3-a 2^2+42*a 3^2
@[expose] def conjugateCoordinates (a : Coordinates) : Coordinates :=
  ![a 0+a 2,-a 1,-a 2,-a 3]

theorem embed_conjugate (a : Coordinates) : embed (conjugateCoordinates a)=star (embed a) := by
  ext <;> simp [embed,conjugateCoordinates] <;> push_cast <;> ring

theorem embed_norm (a : Coordinates) : reducedNorm (embed a)=(integerNorm a:ℚ) := by
  simp only [embed,reducedNorm,integerNorm]
  push_cast
  ring

/-- Actual original integral unit, with its signed quaternion conjugate
as inverse; no normalizer or abstract unit existence premise. -/
@[expose] def unitOfNormOne (a : Coordinates) (ha : integerNorm a=1) : orderˣ where
  val := coordinatesEquiv a
  inv := coordinatesEquiv (conjugateCoordinates a)
  val_inv := by
    apply Subtype.ext
    change embed a*embed (conjugateCoordinates a)=1
    rw [embed_conjugate,norm_identity,embed_norm,ha] <;> simp
  inv_val := by
    apply Subtype.ext
    change embed (conjugateCoordinates a)*embed a=1
    rw [embed_conjugate,norm_identity_left,embed_norm,ha] <;> simp

theorem unitOfNormOne_norm (a : Coordinates) (ha : integerNorm a=1) :
    reducedNorm ((unitOfNormOne a ha:order):B)=1 := by
  change reducedNorm (embed a)=1
  rw [embed_norm,ha] <;> norm_num

@[expose] def baseCoefficients : Fin 8 → Coordinates := ![
  ![-13,-2,0,4],![1,-1,-6,1],![-43,-8,0,14],![13,-1,-14,0],
  ![-29,-6,0,10],![16,-1,-15,0],![5,-1,-6,1],![2,0,-1,0]]
@[expose] def flipFirst (a : Coordinates) : Coordinates := ![a 0,-a 1,a 2,-a 3]
@[expose] def flipSecond (a : Coordinates) : Coordinates := ![-a 0-a 2,a 1+a 3,a 2,-a 3]
@[expose] def signedCoefficients (j : Fin 8) (ε δ : Bool) : Coordinates :=
  let a := if ε then flipFirst (baseCoefficients j) else baseCoefficients j
  if δ then flipSecond a else a

/-- All sign choices are actual original norm-one units. Repeated axis
rows are harmless and retain a uniform complete four-quadrant index set. -/
theorem signed_norm (j : Fin 8) (ε δ : Bool) : integerNorm (signedCoefficients j ε δ)=1 := by
  fin_cases j <;> cases ε <;> cases δ <;>
    norm_num [signedCoefficients,baseCoefficients,flipFirst,flipSecond,integerNorm]

@[expose] def testUnit (j : Fin 8) (ε δ : Bool) : normOneUnits :=
  ⟨unitOfNormOne (signedCoefficients j ε δ) (signed_norm j ε δ),
    (mem_normOneUnits _).mpr (unitOfNormOne_norm _ _)⟩

theorem testUnit_value (j : Fin 8) (ε δ : Bool) :
    (((testUnit j ε δ).val:order):B)=embed (signedCoefficients j ε δ) := rfl

@[expose] def rowConstant : Fin 8 → ℚ := ![672,222,8232,980,4200,1125,222,5]
@[expose] def rowFirst : Fin 8 → ℚ := ![104/5,34/5,1204/5,28,116,30,26/5,0]
@[expose] def rowSecond : Fin 8 → ℚ := ![0,18,1176,168,840,255,66,3]
@[expose] def sign (ε : Bool) : ℚ := if ε then -1 else 1

/-- Exact rational matrix-energy coefficients, before any real square
roots or disk-coordinate normalization is introduced. -/
theorem energy_coefficients (j : Fin 8) (ε δ : Bool) :
    let q := embed (signedCoefficients j ε δ)
    2*q.re^2+420*q.imI^2+10*q.imJ^2+2100*q.imK^2-2=rowConstant j ∧
    4*(q.re*q.imK-q.imI*q.imJ)= -(rowFirst j*sign ε) ∧
    4*q.re*q.imJ+840*q.imI*q.imK= -(rowSecond j*sign δ) := by
  fin_cases j <;> cases ε <;> cases δ <;>
    norm_num [signedCoefficients,baseCoefficients,flipFirst,flipSecond,embed,
      rowConstant,rowFirst,rowSecond,sign]
end PELDirichletOriginalUnits318
