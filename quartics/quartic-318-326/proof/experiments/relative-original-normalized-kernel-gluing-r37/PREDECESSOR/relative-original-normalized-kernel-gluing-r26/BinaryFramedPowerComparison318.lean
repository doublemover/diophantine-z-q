module
public import FramedLineTensorPower318
public import OpenClutchedLocallyFree318
public section
noncomputable section
namespace BinaryFramedPowerComparison318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U V : X.Opens)
  (em : ∀ i : ULift.{u} Bool, SheafOfModules.unit
    ((OpenClutchedLocallyFree318.cover U V i).toScheme.ringCatSheaf) ≅
      M.restrict (OpenClutchedLocallyFree318.cover U V i).ι)
  (en : ∀ i : ULift.{u} Bool, SheafOfModules.unit
    ((OpenClutchedLocallyFree318.cover U V i).toScheme.ringCatSheaf) ≅
      N.restrict (OpenClutchedLocallyFree318.cover U V i).ι)
  (n : ℕ)

/-- On the actual binary cover, the original diagonal identities and
restriction-compatible inverse-frame equation determine all four transition
entries from the forward one. No swapped-overlap identification is assumed. -/
lemma cocycle_power
    (h : (LineFrameCocycle318.cocycle N (OpenClutchedLocallyFree318.cover U V) en).transition
      ⟨false⟩ ⟨true⟩ =
      (LineFrameCocycle318.cocycle M (OpenClutchedLocallyFree318.cover U V) em).transition
        ⟨false⟩ ⟨true⟩ ^ n) :
    LineFrameCocycle318.cocycle N (OpenClutchedLocallyFree318.cover U V) en =
      UnitCocyclePower318.power
        (LineFrameCocycle318.cocycle M (OpenClutchedLocallyFree318.cover U V) em) n := by
  apply UnitTransitionCocycle318.Cocycle.ext
  rintro ⟨i⟩ ⟨j⟩
  cases i <;> cases j
  · change (LineFrameCocycle318.cocycle N _ en).transition ⟨false⟩ ⟨false⟩ =
      (LineFrameCocycle318.cocycle M _ em).transition ⟨false⟩ ⟨false⟩ ^ n
    rw [UnitTransitionCocycle318.Cocycle.diagonal,UnitTransitionCocycle318.Cocycle.diagonal,one_pow]
  · exact h
  · have hswap := congrArg
      (Units.map (X.presheaf.map (homOfLE (show V ⊓ U ≤ U ⊓ V from le_of_eq (inf_comm V U))).op).hom.toMonoidHom) h
    change Units.map _ (LineFrameTransitions318.scalar N _ en ⟨false⟩ ⟨true⟩ (U ⊓ V) _ _) =
      Units.map _ ((LineFrameTransitions318.scalar M _ em ⟨false⟩ ⟨true⟩ (U ⊓ V) _ _) ^ n) at hswap
    rw [map_pow,LineFrameTransitions318.restrict,LineFrameTransitions318.restrict] at hswap
    have hi := congrArg Inv.inv hswap
    change FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame N V (en ⟨true⟩) (V ⊓ U) inf_le_left)
      (OpenLineFrameCoordinates318.frame N U (en ⟨false⟩) (V ⊓ U) inf_le_right) =
      (FrameScalarAlgebra318.scalar
        (OpenLineFrameCoordinates318.frame M V (em ⟨true⟩) (V ⊓ U) inf_le_left)
        (OpenLineFrameCoordinates318.frame M U (em ⟨false⟩) (V ⊓ U) inf_le_right)) ^ n
    rw [FrameScalarAlgebra318.symm
      (OpenLineFrameCoordinates318.frame N U (en ⟨false⟩) (V ⊓ U) inf_le_right)
      (OpenLineFrameCoordinates318.frame N V (en ⟨true⟩) (V ⊓ U) inf_le_left),
      FrameScalarAlgebra318.symm
      (OpenLineFrameCoordinates318.frame M U (em ⟨false⟩) (V ⊓ U) inf_le_right)
      (OpenLineFrameCoordinates318.frame M V (em ⟨true⟩) (V ⊓ U) inf_le_left)]
    simpa only [LineFrameTransitions318.scalar,inv_pow] using hi
  · change (LineFrameCocycle318.cocycle N _ en).transition ⟨true⟩ ⟨true⟩ =
      (LineFrameCocycle318.cocycle M _ em).transition ⟨true⟩ ⟨true⟩ ^ n
    rw [UnitTransitionCocycle318.Cocycle.diagonal,UnitTransitionCocycle318.Cocycle.diagonal,one_pow]

/-- Actual original object comparison, reconstructed through the SAME
binary cocycle. The assumption concerns only original forward frame units. -/
def iso (hc : U ⊔ V = ⊤)
    (h : (LineFrameCocycle318.cocycle N (OpenClutchedLocallyFree318.cover U V) en).transition
      ⟨false⟩ ⟨true⟩ =
      (LineFrameCocycle318.cocycle M (OpenClutchedLocallyFree318.cover U V) em).transition
        ⟨false⟩ ⟨true⟩ ^ n) : FramedLineTensorPower318.object M n ≅ N :=
  FramedLineTensorPower318.iso M (OpenClutchedLocallyFree318.cover U V) em
    (OpenClutchedLocallyFree318.cover_top U V hc) n ≪≫
  (CocycleEqualityTransport318.iso (OpenClutchedLocallyFree318.cover U V)
    (cocycle_power M N U V em en n h)).symm ≪≫
  (LineFrameReconstructionIso318.iso N (OpenClutchedLocallyFree318.cover U V) en
    (OpenClutchedLocallyFree318.cover_top U V hc)).symm
end BinaryFramedPowerComparison318
