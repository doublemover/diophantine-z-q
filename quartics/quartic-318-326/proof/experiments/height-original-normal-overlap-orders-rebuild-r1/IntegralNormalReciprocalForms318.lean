module
public import IntegralNormalTraceForms318
public import ReciprocalUnitDifferentialFrame318
public import IntegralReciprocalNormalClosures318
public section
noncomputable section
namespace IntegralNormalReciprocalForms318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "B" => OpenOrder R a d
local notation "F" => Base R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N
local notation "e" => IntegralNormalSourceDifferentialFrame318.frame R a d

@[expose] def coordinateUnit : Bˣ :=
  Units.map (algebraMap F B).toMonoidHom
    (IntegralReciprocalBase318.tUnit R a (arithmeticDenominator R d))

lemma coordinateUnit_value : (coordinateUnit R a d:B)=
    IntegralNormalSourceDifferentialFrame318.coordinate R a d := by
  change algebraMap F B (IntegralReciprocalBase318.tUnit R a _)=_
  rw [IntegralReciprocalBase318.tUnit_coe]
  rfl

/-- This is the SAME reciprocal scalar map used by the actual normal
infinity chart, not a newly chosen inverse coordinate. -/
lemma reciprocal_polynomial :
    (algebraMap F B) (IntegralReciprocalBase318.backward R a (arithmeticDenominator R d)
      (algebraMap R[X] (IntegralReciprocalBase318.ReciprocalBase R a
        (arithmeticDenominator R d)) X))=(↑(coordinateUnit R a d)⁻¹:B) := by
  change algebraMap F B (IntegralReciprocalBase318.backward R a _
    (IntegralReciprocalBase318.s R a _))=_
  rw [IntegralReciprocalBase318.backward_s]
  rfl

lemma normalized : e (KaehlerDifferential.D R B (coordinateUnit R a d:B))=1 := by
  rw [coordinateUnit_value,IntegralNormalSourceDifferentialFrame318.frame_D]

@[expose] def reciprocalFrame : KaehlerDifferential R B ≃ₗ[B] B :=
  ReciprocalUnitDifferentialFrame318.reciprocalFrame e (coordinateUnit R a d) (normalized R a d)

/-- Every normal trace form has its exact infinity-coordinate coefficient
on the COMMON ORIGINAL source, including its sign and t squared factor.
This does not yet identify the integral reciprocal codifferent lattice. -/
theorem form_transition (z : L) :
    reciprocalFrame R a d (IntegralNormalTraceForms318.form R a d z)=
      -(coordinateUnit R a d:B)^2*z.val := by
  change -(coordinateUnit R a d:B)^2*e (IntegralNormalTraceForms318.form R a d z)=_
  rw [IntegralNormalTraceForms318.coefficient]

theorem form_equality (z : L) : IntegralNormalTraceForms318.form R a d z=
    (-(coordinateUnit R a d:B)^2*z.val) •
      KaehlerDifferential.D R B (↑(coordinateUnit R a d)⁻¹:B) :=
  (ReciprocalUnitDifferentialFrame318.reconstruction e (coordinateUnit R a d)
    (normalized R a d) (IntegralNormalTraceForms318.form R a d z)).symm.trans (by
      rw [IntegralNormalTraceForms318.coefficient])
end IntegralNormalReciprocalForms318
