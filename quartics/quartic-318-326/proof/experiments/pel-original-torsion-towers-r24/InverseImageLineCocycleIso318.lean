module
public import InverseImageLineCocycle318
public import LineFrameReconstructionIso318
public import CocycleEqualityTransport318
public import LinePullbackFrames318
public section
noncomputable section
namespace InverseImageLineCocycleIso318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : X.Modules)
  {ι : Type u} (U : ι → Y.Opens)
  (em : ∀ i, SheafOfModules.unit (f ⁻¹ᵁ U i).toScheme.ringCatSheaf ≅
    M.restrict (f ⁻¹ᵁ U i).ι)
  (en : ∀ i, SheafOfModules.unit (f ⁻¹ᵁ U i).toScheme.ringCatSheaf ≅
    N.restrict (f ⁻¹ᵁ U i).ι)
  (h : InverseImageLineCocycle318.cocycle f M U em =
    InverseImageLineCocycle318.cocycle f N U en)
include h in
lemma source_cocycle :
    LineFrameCocycle318.cocycle M (fun i => f ⁻¹ᵁ U i) em =
      LineFrameCocycle318.cocycle N (fun i => f ⁻¹ᵁ U i) en := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  have he := congrArg (fun c => c.transition i j) h
  simpa only [InverseImageLineCocycle318.cocycle, LineFrameCocycle318.cocycle,
    Scheme.Hom.preimage_inf] using he

/-- Equality of the genuine pushed transition units reconstructs an
isomorphism of the entire source module sheaves, on the true preimage cover. -/
@[expose] def iso (hc : (⊤ : Y.Opens) ≤ ⨆ i, U i) : M ≅ N :=
  LineFrameReconstructionIso318.iso M (fun i => f ⁻¹ᵁ U i) em
    (LinePullbackFrames318.preimage_cover f U hc) ≪≫
  CocycleEqualityTransport318.iso (fun i => f ⁻¹ᵁ U i)
    (source_cocycle f M N U em en h) ≪≫
  (LineFrameReconstructionIso318.iso N (fun i => f ⁻¹ᵁ U i) en
    (LinePullbackFrames318.preimage_cover f U hc)).symm
end InverseImageLineCocycleIso318
