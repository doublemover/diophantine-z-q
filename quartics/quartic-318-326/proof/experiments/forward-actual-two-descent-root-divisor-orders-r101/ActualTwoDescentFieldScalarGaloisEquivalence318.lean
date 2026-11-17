module
public import ActualTwoDescentFieldGlobalCharacterSquareRoot318
public section
noncomputable section
namespace ActualTwoDescentFieldScalarGaloisEquivalence318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentFieldScalarConnectingHom318 ActualTwoDescentFieldScalarConnectingKernel318
open ActualTwoDescentFieldScalarRootCharacters318 ActualTwoDescentFieldScalarRootIndependence318
open ActualTwoDescentFieldGlobalCharacterSquareRoot318 ActualTwoDescentSquareClassQuotient318

lemma actual_scalar_connecting_surjective : Function.Surjective (scalarConnectingHom (F:=F)) := by
  intro χ
  obtain ⟨a,r,hr,hs,hχ⟩ := actual_global_character_square_root χ
  refine ⟨a,?_⟩
  apply Subtype.ext
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  apply Units.ext
  change ((scalarCharacter a σ : Qbarˣ) : Qbar)=(((χ : GalQ →* SquareOne Qbar) σ : Qbarˣ) : Qbar)
  rw [actual_scalar_character_evaluate a r hr hs σ]
  exact hχ σ

/-- Actual scalar Kummer isomorphism, including surjectivity proved from finite Hilbert90 and Krull continuity. -/
def scalarGaloisEquiv : SquareClass F ≃* (continuousCharacters (F:=F)) :=
  (QuotientGroup.quotientMulEquivOfEq (actual_scalar_connecting_kernel (F:=F)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (scalarConnectingHom (F:=F)) (actual_scalar_connecting_surjective (F:=F)))

lemma actual_scalar_galois_value (a : F) (ha : a ≠ 0) :
    (scalarGaloisEquiv (F:=F)) (classOf a ha)=(scalarConnectingHom (F:=F)) (Units.mk0 a ha) := rfl

end ActualTwoDescentFieldScalarGaloisEquivalence318
