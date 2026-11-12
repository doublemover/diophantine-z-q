module
public import ActualTwoDescentGlobalCharacterSquareRoot318
public section
noncomputable section
namespace ActualTwoDescentScalarGaloisEquivalence318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarConnectingHom318 ActualTwoDescentScalarConnectingKernel318
open ActualTwoDescentScalarRootCharacters318 ActualTwoDescentScalarRootIndependence318
open ActualTwoDescentGlobalCharacterSquareRoot318 ActualTwoDescentSquareClassQuotient318

lemma actual_scalar_connecting_surjective : Function.Surjective scalarConnectingHom := by
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
def scalarGaloisEquiv : SquareClass ℚ ≃* continuousCharacters :=
  (QuotientGroup.quotientMulEquivOfEq actual_scalar_connecting_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective scalarConnectingHom actual_scalar_connecting_surjective)

lemma actual_scalar_galois_value (a : ℚ) (ha : a ≠ 0) :
    scalarGaloisEquiv (classOf a ha)=scalarConnectingHom (Units.mk0 a ha) := rfl

end ActualTwoDescentScalarGaloisEquivalence318
