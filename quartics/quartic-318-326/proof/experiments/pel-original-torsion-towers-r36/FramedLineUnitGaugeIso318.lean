module
public import CocycleGaugeIso318
public import LineFrameReconstructionIso318
public section
noncomputable section
namespace FramedLineUnitGaugeIso318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (e : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (d : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hc : (⊤ : X.Opens) ≤ ⨆ i,U i) (a : ∀ i,Γ(X,U i)ˣ)
  (ha : ∀ i j,(LineFrameCocycle318.cocycle N U d).transition i j=
    UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units X).obj U a i j *
      (LineFrameCocycle318.cocycle M U e).transition i j)

/-- A genuine whole module-sheaf isomorphism from an independently
produced REGULAR unit gauge and exact whole-overlap cocycle identity. -/
@[expose] def iso : M ≅ N :=
  LineFrameReconstructionIso318.iso M U e hc ≪≫
    CocycleGaugeIso318.iso U (LineFrameCocycle318.cocycle M U e)
      (LineFrameCocycle318.cocycle N U d) a ha ≪≫
    (LineFrameReconstructionIso318.iso N U d hc).symm
lemma hom_inv : (iso M N U e d hc a ha).hom≫(iso M N U e d hc a ha).inv=𝟙 M :=
  (iso M N U e d hc a ha).hom_inv_id
lemma inv_hom : (iso M N U e d hc a ha).inv≫(iso M N U e d hc a ha).hom=𝟙 N :=
  (iso M N U e d hc a ha).inv_hom_id
end FramedLineUnitGaugeIso318
