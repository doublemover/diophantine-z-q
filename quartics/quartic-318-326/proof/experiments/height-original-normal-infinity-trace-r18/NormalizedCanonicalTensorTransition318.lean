module
public import FourRootDualOverlapTensor318
public import NormalizedWholeDualityFrames318
public import UnitReciprocalDifferential318
public section
noncomputable section
namespace NormalizedCanonicalTensorTransition318
open NormalizedReciprocalLaurent318 NormalizedWholeOverlap318
open FiniteDualModuleAction318 FiniteDualTransport318
open scoped TensorProduct
set_option maxHeartbeats 2200000
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
local notation "L" => Laurent R
local notation "A" => FourRootOrder318.Order (finiteParameter R d a)
local notation "B" => FourRootOrder318.Order (infinityParameter R d a)
local notation "E" => fullOverlap R d a
local notation "F" => FourRootIntegralDuality318.frame (finiteParameter R d a)
local notation "G" => FourRootIntegralDuality318.frame (infinityParameter R d a)

/-- Genuine differential identity on the actual Laurent coordinate base.
This supplies the base differential factor, rather than guessing it from
an abstract degree of a line bundle. -/
theorem coordinate_differential : KaehlerDifferential.D R L (coordinate R:L)=
    -((coordinate R:L)^2) • KaehlerDifferential.D R L (↑(coordinate R)⁻¹:L) := by
  simpa only [inv_inv] using
    (UnitReciprocalDifferential318.differential (R:=R) ((coordinate R)⁻¹))

/-- Actual whole finite-dual transport multiplied by the PROVED Laurent
base differential factor. Identification with a global relative dualizing
sheaf is deliberately not part of this definition or its conclusions. -/
@[expose] def canonicalTransport : Dual L A →ₛₗ[E.toRingEquiv.toRingHom] Dual L B :=
  algebraMap L B (-((coordinate R:L)^2)) • transport E

/-- The finite dual and base differential transformations combine to the
literal -t^-2 generator factor on the entire overlap. -/
theorem canonical_generator : canonicalTransport R d a (frame L A F 1)=
    algebraMap L B (-((↑(coordinate R)⁻¹:L)^2)) • frame L B G 1 := by
  change algebraMap L B (-((coordinate R:L)^2)) •
    transport E (frame L A F 1)=_
  rw [FourRootDualOverlapTensor318.transported_generator,smul_smul,←map_mul]
  congr 1
  congr 1
  rw [mul_comm,NormalizedWholeDualityFrames318.relative_canonical_transition_scalar]

/-- Genuine balanced map on the full tensor squares. -/
@[expose] def canonicalSquare : Square (R:=L) (A:=A) →ₛₗ[E.toRingEquiv.toRingHom]
    Square (R:=L) (A:=B) := TensorProduct.map (canonicalTransport R d a) (canonicalTransport R d a)

theorem canonicalSquare_frame (x : A) :
    canonicalSquare R d a (squareFrame F x)=
      squareFrame G (E x*algebraMap L B ((↑(coordinate R)⁻¹:L)^4)) := by
  rw [squareFrame_scalar,map_smul,squareFrame_one]
  change E x • (canonicalTransport R d a (frame L A F 1) ⊗ₜ[B]
    canonicalTransport R d a (frame L A F 1))=_
  rw [canonical_generator,TensorProduct.smul_tmul_smul,←squareFrame_one,smul_smul,
    squareFrame_scalar]
  congr 1
  rw [←map_mul]
  congr 2
  ring
end NormalizedCanonicalTensorTransition318
