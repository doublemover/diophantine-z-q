module
public import OriginalTensorChartFrameNaturality318
public import FramedLineCocycleIso318
public section
noncomputable section
namespace OriginalFramedComparisonNormalization318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hc : (⊤:X.Opens)≤⨆i,U i)
  (h : LineFrameCocycle318.cocycle M U em=LineFrameCocycle318.cocycle N U en)
local notation "C" => FramedLineCocycleIso318.iso M N U em en hc h
/-- Transpose of the original full coordinate equality. This is an
actual restriction-map equality, not an agreement on pointwise fibers. -/
lemma inverse_frame (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map C.hom ≫ (en i).inv=(em i).inv := by
  apply ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  exact FramedLineCocycleIso318.coordinate M N U em en hc h i
lemma frame (i : ι) :
    em i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso C=en i := by
  apply Iso.ext
  apply (cancel_mono (en i).inv).mp
  simp only [Iso.trans_hom,Functor.mapIso_hom,Category.assoc]
  rw [inverse_frame,(em i).hom_inv_id,(en i).hom_inv_id]
include hc in
/-- Entire morphisms are detected by their complete original coordinate
maps on a genuine cover. No source-section generation assumption is made. -/
lemma hom_ext {P : X.Modules} (a b : P ⟶ N)
    (he : ∀i,a ≫ LineFrameAdjunction318.coordinate N (U i) (en i)=
      b ≫ LineFrameAdjunction318.coordinate N (U i) (en i)) : a=b := by
  apply (cancel_mono (LineFrameReconstructionIso318.iso N U en hc).hom).mp
  apply CocycleModule318.hom_ext U (LineFrameCocycle318.cocycle N U en)
  intro i
  simpa only [Category.assoc,LineFrameReconstructionIso318.hom_coefficient] using he i
include en hc in
/-- A full original cover of target frames detects equality of the
literal restrictions of two arbitrary sheaf morphisms. -/
lemma hom_ext_restrict {P : X.Modules} (a b : P ⟶ N)
    (he : ∀i,(Scheme.Modules.restrictFunctor (U i).ι).map a=
      (Scheme.Modules.restrictFunctor (U i).ι).map b) : a=b := by
  apply hom_ext N U en hc a b
  intro i
  have hh := congrArg (fun q =>
    (Scheme.Modules.restrictAdjunction (U i).ι).homEquiv P
      (SheafOfModules.unit (U i).toScheme.ringCatSheaf) (q ≫ (en i).inv)) (he i)
  simpa only [Adjunction.homEquiv_naturality_left,LineFrameAdjunction318.coordinate] using hh
end OriginalFramedComparisonNormalization318
